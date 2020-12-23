%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VqwnNmr1w1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:11 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 457 expanded)
%              Number of leaves         :   24 ( 134 expanded)
%              Depth                    :   35
%              Number of atoms          : 1450 (8922 expanded)
%              Number of equality atoms :   21 ( 345 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

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

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( X17
       != ( k1_tsep_1 @ X16 @ X15 @ X18 ) )
      | ( ( u1_struct_0 @ X17 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X16 @ X15 @ X18 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X18 ) @ X16 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X18 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X16 @ X15 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
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
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
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
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('33',plain,
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
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( X22 != sk_D_1 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X23: $i] :
      ( ( X23 != sk_D_1 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( m1_subset_1 @ X8 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('68',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('91',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','111'])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( m1_subset_1 @ X8 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('114',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['108','109'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VqwnNmr1w1
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 351 iterations in 0.376s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.83  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.60/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.83  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.60/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.60/0.83  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.60/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.83  thf(t16_tmap_1, conjecture,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.83           ( ![C:$i]:
% 0.60/0.83             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.83               ( ![D:$i]:
% 0.60/0.83                 ( ( m1_subset_1 @
% 0.60/0.83                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.60/0.83                   ( ~( ( ![E:$i]:
% 0.60/0.83                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.60/0.83                            ( ( E ) != ( D ) ) ) ) & 
% 0.60/0.83                        ( ![E:$i]:
% 0.60/0.83                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.83                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i]:
% 0.60/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.83            ( l1_pre_topc @ A ) ) =>
% 0.60/0.83          ( ![B:$i]:
% 0.60/0.83            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.83              ( ![C:$i]:
% 0.60/0.83                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.83                  ( ![D:$i]:
% 0.60/0.83                    ( ( m1_subset_1 @
% 0.60/0.83                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.60/0.83                      ( ~( ( ![E:$i]:
% 0.60/0.83                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.60/0.83                               ( ( E ) != ( D ) ) ) ) & 
% 0.60/0.83                           ( ![E:$i]:
% 0.60/0.83                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.83                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 0.60/0.83  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(dt_k1_tsep_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.60/0.83         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.60/0.83         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.83       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.60/0.83         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.60/0.83         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X19)
% 0.60/0.83          | ~ (l1_pre_topc @ X20)
% 0.60/0.83          | (v2_struct_0 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X21)
% 0.60/0.83          | ~ (m1_pre_topc @ X21 @ X20)
% 0.60/0.83          | (m1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X21) @ X20))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.60/0.83  thf('4', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.60/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ X0)
% 0.60/0.83          | (v2_struct_0 @ sk_A)
% 0.60/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.83  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('6', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.60/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ X0)
% 0.60/0.83          | (v2_struct_0 @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.60/0.83  thf('7', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['1', '6'])).
% 0.60/0.83  thf(dt_m1_pre_topc, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( l1_pre_topc @ A ) =>
% 0.60/0.83       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.60/0.83  thf('8', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X12 @ X13)
% 0.60/0.83          | (l1_pre_topc @ X12)
% 0.60/0.83          | ~ (l1_pre_topc @ X13))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.60/0.83  thf('9', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.83  thf(dt_l1_pre_topc, axiom,
% 0.60/0.83    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.83  thf('13', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['11', '12'])).
% 0.60/0.83  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X19)
% 0.60/0.83          | ~ (l1_pre_topc @ X20)
% 0.60/0.83          | (v2_struct_0 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X21)
% 0.60/0.83          | ~ (m1_pre_topc @ X21 @ X20)
% 0.60/0.83          | (v1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X21)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.60/0.83  thf('17', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 0.60/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ X0)
% 0.60/0.83          | (v2_struct_0 @ sk_A)
% 0.60/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.83  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('19', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 0.60/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ X0)
% 0.60/0.83          | (v2_struct_0 @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['17', '18'])).
% 0.60/0.83  thf('20', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['14', '19'])).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['1', '6'])).
% 0.60/0.83  thf(d2_tsep_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.83           ( ![C:$i]:
% 0.60/0.83             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.83               ( ![D:$i]:
% 0.60/0.83                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.60/0.83                     ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.83                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.60/0.83                     ( ( u1_struct_0 @ D ) =
% 0.60/0.83                       ( k2_xboole_0 @
% 0.60/0.83                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf('22', plain,
% 0.60/0.83      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.83         ((v2_struct_0 @ X15)
% 0.60/0.83          | ~ (m1_pre_topc @ X15 @ X16)
% 0.60/0.83          | (v2_struct_0 @ X17)
% 0.60/0.83          | ~ (v1_pre_topc @ X17)
% 0.60/0.83          | ~ (m1_pre_topc @ X17 @ X16)
% 0.60/0.83          | ((X17) != (k1_tsep_1 @ X16 @ X15 @ X18))
% 0.60/0.83          | ((u1_struct_0 @ X17)
% 0.60/0.83              = (k2_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X18)))
% 0.60/0.83          | ~ (m1_pre_topc @ X18 @ X16)
% 0.60/0.83          | (v2_struct_0 @ X18)
% 0.60/0.83          | ~ (l1_pre_topc @ X16)
% 0.60/0.83          | (v2_struct_0 @ X16))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.60/0.83  thf('23', plain,
% 0.60/0.83      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.60/0.83         ((v2_struct_0 @ X16)
% 0.60/0.83          | ~ (l1_pre_topc @ X16)
% 0.60/0.83          | (v2_struct_0 @ X18)
% 0.60/0.83          | ~ (m1_pre_topc @ X18 @ X16)
% 0.60/0.83          | ((u1_struct_0 @ (k1_tsep_1 @ X16 @ X15 @ X18))
% 0.60/0.83              = (k2_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X18)))
% 0.60/0.83          | ~ (m1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X18) @ X16)
% 0.60/0.83          | ~ (v1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X18))
% 0.60/0.83          | (v2_struct_0 @ (k1_tsep_1 @ X16 @ X15 @ X18))
% 0.60/0.83          | ~ (m1_pre_topc @ X15 @ X16)
% 0.60/0.83          | (v2_struct_0 @ X15))),
% 0.60/0.83      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.83  thf('24', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['21', '23'])).
% 0.60/0.83  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('28', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A))),
% 0.60/0.83      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.60/0.83  thf('29', plain,
% 0.60/0.83      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['28'])).
% 0.60/0.83  thf('30', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['20', '29'])).
% 0.60/0.83  thf('31', plain,
% 0.60/0.83      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['30'])).
% 0.60/0.83  thf('32', plain,
% 0.60/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X19)
% 0.60/0.83          | ~ (l1_pre_topc @ X20)
% 0.60/0.83          | (v2_struct_0 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X21)
% 0.60/0.83          | ~ (m1_pre_topc @ X21 @ X20)
% 0.60/0.83          | ~ (v2_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X21)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.60/0.83  thf('33', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.83  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('37', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.60/0.83  thf('38', plain,
% 0.60/0.83      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.83  thf('39', plain,
% 0.60/0.83      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(d2_subset_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ( v1_xboole_0 @ A ) =>
% 0.60/0.83         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.60/0.83       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.83         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.83  thf('40', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (~ (m1_subset_1 @ X6 @ X7)
% 0.60/0.83          | (r2_hidden @ X6 @ X7)
% 0.60/0.83          | (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('41', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ 
% 0.60/0.83           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.83  thf('42', plain,
% 0.60/0.83      (((r2_hidden @ sk_D_1 @ 
% 0.60/0.83         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.60/0.83      inference('sup+', [status(thm)], ['38', '41'])).
% 0.60/0.83  thf(d3_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.60/0.83       ( ![D:$i]:
% 0.60/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.83           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.60/0.83  thf('43', plain,
% 0.60/0.83      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X4 @ X2)
% 0.60/0.83          | (r2_hidden @ X4 @ X3)
% 0.60/0.83          | (r2_hidden @ X4 @ X1)
% 0.60/0.83          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.60/0.83      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.60/0.83  thf('44', plain,
% 0.60/0.83      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.60/0.83         ((r2_hidden @ X4 @ X1)
% 0.60/0.83          | (r2_hidden @ X4 @ X3)
% 0.60/0.83          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['43'])).
% 0.60/0.83  thf('45', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['42', '44'])).
% 0.60/0.83  thf(fc2_struct_0, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.60/0.83       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.83  thf('46', plain,
% 0.60/0.83      (![X14 : $i]:
% 0.60/0.83         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.60/0.83          | ~ (l1_struct_0 @ X14)
% 0.60/0.83          | (v2_struct_0 @ X14))),
% 0.60/0.83      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.60/0.83  thf('47', plain,
% 0.60/0.83      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.83  thf('48', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['13', '47'])).
% 0.60/0.83  thf('49', plain,
% 0.60/0.83      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['48'])).
% 0.60/0.83  thf('50', plain,
% 0.60/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X19)
% 0.60/0.83          | ~ (l1_pre_topc @ X20)
% 0.60/0.83          | (v2_struct_0 @ X20)
% 0.60/0.83          | (v2_struct_0 @ X21)
% 0.60/0.83          | ~ (m1_pre_topc @ X21 @ X20)
% 0.60/0.83          | ~ (v2_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X21)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.60/0.83  thf('51', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['49', '50'])).
% 0.60/0.83  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('55', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.60/0.83  thf('56', plain,
% 0.60/0.83      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['55'])).
% 0.60/0.83  thf('57', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X6 @ X7)
% 0.60/0.83          | (m1_subset_1 @ X6 @ X7)
% 0.60/0.83          | (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('58', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['56', '57'])).
% 0.60/0.83  thf('59', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X6 @ X7)
% 0.60/0.83          | (m1_subset_1 @ X6 @ X7)
% 0.60/0.83          | (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('60', plain,
% 0.60/0.83      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['58', '59'])).
% 0.60/0.83  thf('61', plain,
% 0.60/0.83      (![X22 : $i]:
% 0.60/0.83         (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('62', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.60/0.83  thf('63', plain,
% 0.60/0.83      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['60', '62'])).
% 0.60/0.83  thf('64', plain,
% 0.60/0.83      (![X23 : $i]:
% 0.60/0.83         (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('65', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.60/0.83      inference('simplify', [status(thm)], ['64'])).
% 0.60/0.83  thf('66', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['63', '65'])).
% 0.60/0.83  thf('67', plain,
% 0.60/0.83      (![X7 : $i, X8 : $i]:
% 0.60/0.83         (~ (v1_xboole_0 @ X8) | (m1_subset_1 @ X8 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('68', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.60/0.83  thf('69', plain,
% 0.60/0.83      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)) | ~ (v1_xboole_0 @ sk_D_1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.83  thf('70', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['42', '44'])).
% 0.60/0.83  thf('71', plain,
% 0.60/0.83      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('72', plain,
% 0.60/0.83      (![X7 : $i, X8 : $i]:
% 0.60/0.83         (~ (m1_subset_1 @ X8 @ X7) | (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('73', plain,
% 0.60/0.83      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['71', '72'])).
% 0.60/0.83  thf('74', plain,
% 0.60/0.83      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['70', '73'])).
% 0.60/0.83  thf('75', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X6 @ X7)
% 0.60/0.83          | (m1_subset_1 @ X6 @ X7)
% 0.60/0.83          | (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('76', plain,
% 0.60/0.83      (((v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['74', '75'])).
% 0.60/0.83  thf('77', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X6 @ X7)
% 0.60/0.83          | (m1_subset_1 @ X6 @ X7)
% 0.60/0.83          | (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('78', plain,
% 0.60/0.83      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['76', '77'])).
% 0.60/0.83  thf('79', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.60/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.60/0.83  thf('80', plain,
% 0.60/0.83      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['78', '79'])).
% 0.60/0.83  thf('81', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.60/0.83      inference('simplify', [status(thm)], ['64'])).
% 0.60/0.83  thf('82', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['80', '81'])).
% 0.60/0.83  thf('83', plain,
% 0.60/0.83      (![X14 : $i]:
% 0.60/0.83         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.60/0.83          | ~ (l1_struct_0 @ X14)
% 0.60/0.83          | (v2_struct_0 @ X14))),
% 0.60/0.83      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.60/0.83  thf('84', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | ~ (l1_struct_0 @ sk_C))),
% 0.60/0.83      inference('sup-', [status(thm)], ['82', '83'])).
% 0.60/0.83  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('86', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X12 @ X13)
% 0.60/0.83          | (l1_pre_topc @ X12)
% 0.60/0.83          | ~ (l1_pre_topc @ X13))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.60/0.83  thf('87', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.60/0.83      inference('sup-', [status(thm)], ['85', '86'])).
% 0.60/0.83  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('89', plain, ((l1_pre_topc @ sk_C)),
% 0.60/0.83      inference('demod', [status(thm)], ['87', '88'])).
% 0.60/0.83  thf('90', plain,
% 0.60/0.83      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.83  thf('91', plain, ((l1_struct_0 @ sk_C)),
% 0.60/0.83      inference('sup-', [status(thm)], ['89', '90'])).
% 0.60/0.83  thf('92', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('demod', [status(thm)], ['84', '91'])).
% 0.60/0.83  thf('93', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['92'])).
% 0.60/0.83  thf('94', plain,
% 0.60/0.83      (![X14 : $i]:
% 0.60/0.83         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.60/0.83          | ~ (l1_struct_0 @ X14)
% 0.60/0.83          | (v2_struct_0 @ X14))),
% 0.60/0.83      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.60/0.83  thf('95', plain,
% 0.60/0.83      (((v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | ~ (l1_struct_0 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['93', '94'])).
% 0.60/0.83  thf('96', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('97', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i]:
% 0.60/0.83         (~ (m1_pre_topc @ X12 @ X13)
% 0.60/0.83          | (l1_pre_topc @ X12)
% 0.60/0.83          | ~ (l1_pre_topc @ X13))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.60/0.83  thf('98', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['96', '97'])).
% 0.60/0.83  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.83      inference('demod', [status(thm)], ['98', '99'])).
% 0.60/0.83  thf('101', plain,
% 0.60/0.83      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.83  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.60/0.83      inference('sup-', [status(thm)], ['100', '101'])).
% 0.60/0.83  thf('103', plain,
% 0.60/0.83      (((v1_xboole_0 @ sk_D_1)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['95', '102'])).
% 0.60/0.83  thf('104', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B)
% 0.60/0.83        | (v1_xboole_0 @ sk_D_1))),
% 0.60/0.83      inference('simplify', [status(thm)], ['103'])).
% 0.60/0.83  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('106', plain,
% 0.60/0.83      (((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('sup-', [status(thm)], ['104', '105'])).
% 0.60/0.83  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('108', plain, (((v2_struct_0 @ sk_C) | (v1_xboole_0 @ sk_D_1))),
% 0.60/0.83      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.83  thf('109', plain, (~ (v2_struct_0 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('110', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.60/0.83      inference('clc', [status(thm)], ['108', '109'])).
% 0.60/0.83  thf('111', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.60/0.83      inference('demod', [status(thm)], ['69', '110'])).
% 0.60/0.83  thf('112', plain,
% 0.60/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.60/0.83        | (v2_struct_0 @ sk_C)
% 0.60/0.83        | (v2_struct_0 @ sk_A)
% 0.60/0.83        | (v2_struct_0 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['66', '111'])).
% 0.60/0.83  thf('113', plain,
% 0.60/0.83      (![X7 : $i, X8 : $i]:
% 0.60/0.83         (~ (v1_xboole_0 @ X8) | (m1_subset_1 @ X8 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.83  thf('114', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.60/0.83      inference('simplify', [status(thm)], ['64'])).
% 0.60/0.83  thf('115', plain,
% 0.60/0.83      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (v1_xboole_0 @ sk_D_1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['113', '114'])).
% 0.60/0.83  thf('116', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.60/0.83      inference('clc', [status(thm)], ['108', '109'])).
% 0.60/0.83  thf('117', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.60/0.83      inference('demod', [status(thm)], ['115', '116'])).
% 0.60/0.83  thf('118', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.60/0.83      inference('sup-', [status(thm)], ['112', '117'])).
% 0.60/0.83  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('120', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.60/0.83      inference('clc', [status(thm)], ['118', '119'])).
% 0.60/0.83  thf('121', plain, (~ (v2_struct_0 @ sk_C)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('122', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('clc', [status(thm)], ['120', '121'])).
% 0.60/0.83  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.60/0.83  
% 0.60/0.83  % SZS output end Refutation
% 0.60/0.83  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
