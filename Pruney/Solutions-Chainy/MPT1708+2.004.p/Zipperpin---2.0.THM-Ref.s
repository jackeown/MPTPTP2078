%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Elli5D1yp

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:13 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  206 (1376 expanded)
%              Number of leaves         :   27 ( 379 expanded)
%              Depth                    :   45
%              Number of atoms          : 2168 (30820 expanded)
%              Number of equality atoms :   56 (1222 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(t17_tmap_1,conjecture,(
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
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                   => ( ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                      & ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

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
               => ( ~ ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                     => ( ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                        & ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
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
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
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
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tsep_1 @ X15 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( X18
       != ( k2_tsep_1 @ X16 @ X15 @ X17 ) )
      | ( ( u1_struct_0 @ X18 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X16 @ X15 @ X17 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X16 @ X15 @ X17 ) @ X16 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X16 @ X15 @ X17 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X16 @ X15 @ X17 ) )
      | ( r1_tsep_1 @ X15 @ X17 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r2_hidden @ sk_D_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('72',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) )
      | ( X22 != sk_D_1 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) )
      | ( X23 != sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('88',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( m1_subset_1 @ X10 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('97',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('99',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','125'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ~ ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) )
    | ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('135',plain,(
    ! [X23: $i] :
      ( ( X23 != sk_D_1 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['86','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','136'])).

thf('138',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( m1_subset_1 @ X10 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('141',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('142',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X23: $i] :
      ( ( X23 != sk_D_1 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['133','134'])).

thf('144',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('146',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('147',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('149',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['86','135'])).

thf('151',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['155','162'])).

thf('164',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['139','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['0','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Elli5D1yp
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 462 iterations in 0.339s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.77  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.59/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.77  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.59/0.77  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.59/0.77  thf(t17_tmap_1, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.77               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.59/0.77                 ( ![D:$i]:
% 0.59/0.77                   ( ( m1_subset_1 @
% 0.59/0.77                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.59/0.77                     ( ( ?[E:$i]:
% 0.59/0.77                         ( ( ( E ) = ( D ) ) & 
% 0.59/0.77                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.59/0.77                       ( ?[E:$i]:
% 0.59/0.77                         ( ( ( E ) = ( D ) ) & 
% 0.59/0.77                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.77            ( l1_pre_topc @ A ) ) =>
% 0.59/0.77          ( ![B:$i]:
% 0.59/0.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.77              ( ![C:$i]:
% 0.59/0.77                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.77                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.59/0.77                    ( ![D:$i]:
% 0.59/0.77                      ( ( m1_subset_1 @
% 0.59/0.77                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.59/0.77                        ( ( ?[E:$i]:
% 0.59/0.77                            ( ( ( E ) = ( D ) ) & 
% 0.59/0.77                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.59/0.77                          ( ?[E:$i]:
% 0.59/0.77                            ( ( ( E ) = ( D ) ) & 
% 0.59/0.77                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 0.59/0.77  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(dt_k2_tsep_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.59/0.77         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.59/0.77         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.77       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 0.59/0.77         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.59/0.77         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X19 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X19)
% 0.59/0.77          | ~ (l1_pre_topc @ X20)
% 0.59/0.77          | (v2_struct_0 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X21)
% 0.59/0.77          | ~ (m1_pre_topc @ X21 @ X20)
% 0.59/0.77          | (m1_pre_topc @ (k2_tsep_1 @ X20 @ X19 @ X21) @ X20))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.59/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ X0)
% 0.59/0.77          | (v2_struct_0 @ sk_A)
% 0.59/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.59/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ X0)
% 0.59/0.77          | (v2_struct_0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '6'])).
% 0.59/0.77  thf(dt_m1_pre_topc, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( l1_pre_topc @ A ) =>
% 0.59/0.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X12 @ X13)
% 0.59/0.77          | (l1_pre_topc @ X12)
% 0.59/0.77          | ~ (l1_pre_topc @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.77  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf(dt_l1_pre_topc, axiom,
% 0.59/0.77    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.77  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X19 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X19)
% 0.59/0.77          | ~ (l1_pre_topc @ X20)
% 0.59/0.77          | (v2_struct_0 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X21)
% 0.59/0.77          | ~ (m1_pre_topc @ X21 @ X20)
% 0.59/0.77          | (v1_pre_topc @ (k2_tsep_1 @ X20 @ X19 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.59/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ X0)
% 0.59/0.77          | (v2_struct_0 @ sk_A)
% 0.59/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.77  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.59/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ X0)
% 0.59/0.77          | (v2_struct_0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['18', '19'])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['15', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '6'])).
% 0.59/0.77  thf(d5_tsep_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.77               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.59/0.77                 ( ![D:$i]:
% 0.59/0.77                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.59/0.77                       ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.77                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 0.59/0.77                       ( ( u1_struct_0 @ D ) =
% 0.59/0.77                         ( k3_xboole_0 @
% 0.59/0.77                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         ((v2_struct_0 @ X15)
% 0.59/0.77          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.77          | (r1_tsep_1 @ X15 @ X17)
% 0.59/0.77          | (v2_struct_0 @ X18)
% 0.59/0.77          | ~ (v1_pre_topc @ X18)
% 0.59/0.77          | ~ (m1_pre_topc @ X18 @ X16)
% 0.59/0.77          | ((X18) != (k2_tsep_1 @ X16 @ X15 @ X17))
% 0.59/0.77          | ((u1_struct_0 @ X18)
% 0.59/0.77              = (k3_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17)))
% 0.59/0.77          | ~ (m1_pre_topc @ X17 @ X16)
% 0.59/0.77          | (v2_struct_0 @ X17)
% 0.59/0.77          | ~ (l1_pre_topc @ X16)
% 0.59/0.77          | (v2_struct_0 @ X16))),
% 0.59/0.77      inference('cnf', [status(esa)], [d5_tsep_1])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.77         ((v2_struct_0 @ X16)
% 0.59/0.77          | ~ (l1_pre_topc @ X16)
% 0.59/0.77          | (v2_struct_0 @ X17)
% 0.59/0.77          | ~ (m1_pre_topc @ X17 @ X16)
% 0.59/0.77          | ((u1_struct_0 @ (k2_tsep_1 @ X16 @ X15 @ X17))
% 0.59/0.77              = (k3_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17)))
% 0.59/0.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ X16 @ X15 @ X17) @ X16)
% 0.59/0.77          | ~ (v1_pre_topc @ (k2_tsep_1 @ X16 @ X15 @ X17))
% 0.59/0.77          | (v2_struct_0 @ (k2_tsep_1 @ X16 @ X15 @ X17))
% 0.59/0.77          | (r1_tsep_1 @ X15 @ X17)
% 0.59/0.77          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.77          | (v2_struct_0 @ X15))),
% 0.59/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['22', '24'])).
% 0.59/0.77  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['21', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X19 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X19)
% 0.59/0.77          | ~ (l1_pre_topc @ X20)
% 0.59/0.77          | (v2_struct_0 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X21)
% 0.59/0.77          | ~ (m1_pre_topc @ X21 @ X20)
% 0.59/0.77          | ~ (v2_struct_0 @ (k2_tsep_1 @ X20 @ X19 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.77  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['38'])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(d2_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.59/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.59/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X8 @ X9)
% 0.59/0.77          | (r2_hidden @ X8 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ 
% 0.59/0.77           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ 
% 0.59/0.77         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['39', '42'])).
% 0.59/0.77  thf(t48_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.59/0.77           = (k3_xboole_0 @ X6 @ X7))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf(d5_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.59/0.77       ( ![D:$i]:
% 0.59/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.77           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.59/0.77  thf('45', plain,
% 0.59/0.77      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X4 @ X3)
% 0.59/0.77          | (r2_hidden @ X4 @ X1)
% 0.59/0.77          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.59/0.77         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['45'])).
% 0.59/0.77  thf('47', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['44', '46'])).
% 0.59/0.77  thf('48', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['43', '47'])).
% 0.59/0.77  thf(fc2_struct_0, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.77       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.77  thf('49', plain,
% 0.59/0.77      (![X14 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.59/0.77          | ~ (l1_struct_0 @ X14)
% 0.59/0.77          | (v2_struct_0 @ X14))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.77  thf('51', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['14', '50'])).
% 0.59/0.77  thf('52', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['51'])).
% 0.59/0.77  thf('53', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X19 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X19)
% 0.59/0.77          | ~ (l1_pre_topc @ X20)
% 0.59/0.77          | (v2_struct_0 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X21)
% 0.59/0.77          | ~ (m1_pre_topc @ X21 @ X20)
% 0.59/0.77          | ~ (v2_struct_0 @ (k2_tsep_1 @ X20 @ X19 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.77  thf('54', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.77  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('58', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.59/0.77  thf('59', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['58'])).
% 0.59/0.77  thf('60', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.77          | (r2_hidden @ X0 @ X2)
% 0.59/0.77          | (r2_hidden @ X0 @ X3)
% 0.59/0.77          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.77  thf('61', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.59/0.77          | (r2_hidden @ X0 @ X2)
% 0.59/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.77      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.77  thf('62', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v2_struct_0 @ sk_C)
% 0.59/0.77          | (v2_struct_0 @ sk_A)
% 0.59/0.77          | (v2_struct_0 @ sk_B)
% 0.59/0.77          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77          | (r2_hidden @ sk_D_1 @ X0)
% 0.59/0.77          | (r2_hidden @ sk_D_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['59', '61'])).
% 0.59/0.77  thf('63', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ 
% 0.59/0.77         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.77      inference('sup+', [status(thm)], ['39', '42'])).
% 0.59/0.77  thf('64', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.59/0.77           = (k3_xboole_0 @ X6 @ X7))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('65', plain,
% 0.59/0.77      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X4 @ X3)
% 0.59/0.77          | ~ (r2_hidden @ X4 @ X2)
% 0.59/0.77          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.77  thf('66', plain,
% 0.59/0.77      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X4 @ X2)
% 0.59/0.77          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['65'])).
% 0.59/0.77  thf('67', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['64', '66'])).
% 0.59/0.77  thf('68', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | ~ (r2_hidden @ sk_D_1 @ 
% 0.59/0.77             (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['63', '67'])).
% 0.59/0.77  thf('69', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['62', '68'])).
% 0.59/0.77  thf('70', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.77  thf('71', plain,
% 0.59/0.77      (![X14 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.59/0.77          | ~ (l1_struct_0 @ X14)
% 0.59/0.77          | (v2_struct_0 @ X14))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.77  thf('72', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.77  thf('73', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['13', '72'])).
% 0.59/0.77  thf('74', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.59/0.77  thf('75', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X19 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X19)
% 0.59/0.77          | ~ (l1_pre_topc @ X20)
% 0.59/0.77          | (v2_struct_0 @ X20)
% 0.59/0.77          | (v2_struct_0 @ X21)
% 0.59/0.77          | ~ (m1_pre_topc @ X21 @ X20)
% 0.59/0.77          | ~ (v2_struct_0 @ (k2_tsep_1 @ X20 @ X19 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.77  thf('76', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.59/0.77  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('79', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('80', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.59/0.77  thf('81', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['80'])).
% 0.59/0.77  thf('82', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X8 @ X9)
% 0.59/0.77          | (m1_subset_1 @ X8 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('83', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['81', '82'])).
% 0.59/0.77  thf('84', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B))
% 0.59/0.77          | ((X22) != (sk_D_1))
% 0.59/0.77          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C))
% 0.59/0.77          | ((X23) != (sk_D_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('85', plain,
% 0.59/0.77      ((![X23 : $i]:
% 0.59/0.77          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C))))
% 0.59/0.77         <= ((![X23 : $i]:
% 0.59/0.77                (((X23) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.77      inference('split', [status(esa)], ['84'])).
% 0.59/0.77  thf('86', plain,
% 0.59/0.77      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.59/0.77         <= ((![X23 : $i]:
% 0.59/0.77                (((X23) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['85'])).
% 0.59/0.77  thf('87', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('simplify', [status(thm)], ['58'])).
% 0.59/0.77  thf('88', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X8 @ X9)
% 0.59/0.77          | (m1_subset_1 @ X8 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('89', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['87', '88'])).
% 0.59/0.77  thf('90', plain,
% 0.59/0.77      ((![X22 : $i]:
% 0.59/0.77          (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B))))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('split', [status(esa)], ['84'])).
% 0.59/0.77  thf('91', plain,
% 0.59/0.77      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['90'])).
% 0.59/0.77  thf('92', plain,
% 0.59/0.77      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.77         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_C)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['89', '91'])).
% 0.59/0.77  thf('93', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('94', plain,
% 0.59/0.77      ((((v2_struct_0 @ sk_C)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['92', '93'])).
% 0.59/0.77  thf('95', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ X10)
% 0.59/0.77          | (m1_subset_1 @ X10 @ X9)
% 0.59/0.77          | ~ (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('96', plain,
% 0.59/0.77      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['90'])).
% 0.59/0.77  thf('97', plain,
% 0.59/0.77      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (v1_xboole_0 @ sk_D_1)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['95', '96'])).
% 0.59/0.77  thf('98', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['43', '47'])).
% 0.59/0.77  thf('99', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('100', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X10 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X10)
% 0.59/0.77          | ~ (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('101', plain,
% 0.59/0.77      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['99', '100'])).
% 0.59/0.77  thf('102', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['98', '101'])).
% 0.59/0.77  thf('103', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X8 @ X9)
% 0.59/0.77          | (m1_subset_1 @ X8 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('104', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_D_1)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.77        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['102', '103'])).
% 0.59/0.77  thf('105', plain,
% 0.59/0.77      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['90'])).
% 0.59/0.77  thf('106', plain,
% 0.59/0.77      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.77         | (v2_struct_0 @ sk_C)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77         | (v1_xboole_0 @ sk_D_1)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['104', '105'])).
% 0.59/0.77  thf('107', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('108', plain,
% 0.59/0.77      ((((v1_xboole_0 @ sk_D_1)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_C)
% 0.59/0.77         | (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['106', '107'])).
% 0.59/0.77  thf('109', plain,
% 0.59/0.77      (![X14 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.59/0.77          | ~ (l1_struct_0 @ X14)
% 0.59/0.77          | (v2_struct_0 @ X14))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.77  thf('110', plain,
% 0.59/0.77      ((((v2_struct_0 @ sk_C)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (v1_xboole_0 @ sk_D_1)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | ~ (l1_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['108', '109'])).
% 0.59/0.77  thf('111', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('112', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X12 @ X13)
% 0.59/0.77          | (l1_pre_topc @ X12)
% 0.59/0.77          | ~ (l1_pre_topc @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.77  thf('113', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['111', '112'])).
% 0.59/0.77  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('115', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.77      inference('demod', [status(thm)], ['113', '114'])).
% 0.59/0.77  thf('116', plain,
% 0.59/0.77      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.77  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.77      inference('sup-', [status(thm)], ['115', '116'])).
% 0.59/0.77  thf('118', plain,
% 0.59/0.77      ((((v2_struct_0 @ sk_C)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (v1_xboole_0 @ sk_D_1)
% 0.59/0.77         | (v2_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('demod', [status(thm)], ['110', '117'])).
% 0.59/0.77  thf('119', plain,
% 0.59/0.77      ((((v1_xboole_0 @ sk_D_1)
% 0.59/0.77         | (v2_struct_0 @ sk_B)
% 0.59/0.77         | (v2_struct_0 @ sk_A)
% 0.59/0.77         | (v2_struct_0 @ sk_C)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['118'])).
% 0.59/0.77  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('121', plain,
% 0.59/0.77      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v1_xboole_0 @ sk_D_1)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['119', '120'])).
% 0.59/0.77  thf('122', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('123', plain,
% 0.59/0.77      ((((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('clc', [status(thm)], ['121', '122'])).
% 0.59/0.77  thf('124', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('125', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_D_1))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('clc', [status(thm)], ['123', '124'])).
% 0.59/0.77  thf('126', plain,
% 0.59/0.77      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('demod', [status(thm)], ['97', '125'])).
% 0.59/0.77  thf('127', plain,
% 0.59/0.77      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['94', '126'])).
% 0.59/0.77  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('129', plain,
% 0.59/0.77      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('clc', [status(thm)], ['127', '128'])).
% 0.59/0.77  thf('130', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('131', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_A))
% 0.59/0.77         <= ((![X22 : $i]:
% 0.59/0.77                (((X22) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.77      inference('clc', [status(thm)], ['129', '130'])).
% 0.59/0.77  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('133', plain,
% 0.59/0.77      (~
% 0.59/0.77       (![X22 : $i]:
% 0.59/0.77          (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['131', '132'])).
% 0.59/0.77  thf('134', plain,
% 0.59/0.77      ((![X23 : $i]:
% 0.59/0.77          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C)))) | 
% 0.59/0.77       (![X22 : $i]:
% 0.59/0.77          (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B))))),
% 0.59/0.77      inference('split', [status(esa)], ['84'])).
% 0.59/0.77  thf('135', plain,
% 0.59/0.77      ((![X23 : $i]:
% 0.59/0.77          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C))))),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['133', '134'])).
% 0.59/0.77  thf('136', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['86', '135'])).
% 0.59/0.77  thf('137', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['83', '136'])).
% 0.59/0.77  thf('138', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('139', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['137', '138'])).
% 0.59/0.77  thf('140', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ X10)
% 0.59/0.77          | (m1_subset_1 @ X10 @ X9)
% 0.59/0.77          | ~ (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('141', plain,
% 0.59/0.77      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.59/0.77         <= ((![X23 : $i]:
% 0.59/0.77                (((X23) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['85'])).
% 0.59/0.77  thf('142', plain,
% 0.59/0.77      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)) | ~ (v1_xboole_0 @ sk_D_1)))
% 0.59/0.77         <= ((![X23 : $i]:
% 0.59/0.77                (((X23) != (sk_D_1))
% 0.59/0.77                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['140', '141'])).
% 0.59/0.77  thf('143', plain,
% 0.59/0.77      ((![X23 : $i]:
% 0.59/0.77          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_C))))),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['133', '134'])).
% 0.59/0.77  thf('144', plain,
% 0.59/0.77      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)) | ~ (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['142', '143'])).
% 0.59/0.77  thf('145', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.77  thf('146', plain,
% 0.59/0.77      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['99', '100'])).
% 0.59/0.77  thf('147', plain,
% 0.59/0.77      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['145', '146'])).
% 0.59/0.77  thf('148', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X8 @ X9)
% 0.59/0.77          | (m1_subset_1 @ X8 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.77  thf('149', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_D_1)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['147', '148'])).
% 0.59/0.77  thf('150', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['86', '135'])).
% 0.59/0.77  thf('151', plain,
% 0.59/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['149', '150'])).
% 0.59/0.77  thf('152', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('153', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_D_1)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B)
% 0.59/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['151', '152'])).
% 0.59/0.77  thf('154', plain,
% 0.59/0.77      (![X14 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.59/0.77          | ~ (l1_struct_0 @ X14)
% 0.59/0.77          | (v2_struct_0 @ X14))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.77  thf('155', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | ~ (l1_struct_0 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['153', '154'])).
% 0.59/0.77  thf('156', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('157', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (~ (m1_pre_topc @ X12 @ X13)
% 0.59/0.77          | (l1_pre_topc @ X12)
% 0.59/0.77          | ~ (l1_pre_topc @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.77  thf('158', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['156', '157'])).
% 0.59/0.77  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('160', plain, ((l1_pre_topc @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['158', '159'])).
% 0.59/0.77  thf('161', plain,
% 0.59/0.77      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.77  thf('162', plain, ((l1_struct_0 @ sk_C)),
% 0.59/0.77      inference('sup-', [status(thm)], ['160', '161'])).
% 0.59/0.77  thf('163', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v1_xboole_0 @ sk_D_1)
% 0.59/0.77        | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['155', '162'])).
% 0.59/0.77  thf('164', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_D_1)
% 0.59/0.77        | (v2_struct_0 @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ sk_A)
% 0.59/0.77        | (v2_struct_0 @ sk_B))),
% 0.59/0.77      inference('simplify', [status(thm)], ['163'])).
% 0.59/0.77  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('166', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['164', '165'])).
% 0.59/0.77  thf('167', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('168', plain, (((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('clc', [status(thm)], ['166', '167'])).
% 0.59/0.77  thf('169', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('170', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.59/0.77      inference('clc', [status(thm)], ['168', '169'])).
% 0.59/0.77  thf('171', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['144', '170'])).
% 0.59/0.77  thf('172', plain,
% 0.59/0.77      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['139', '171'])).
% 0.59/0.77  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('174', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['172', '173'])).
% 0.59/0.77  thf('175', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('176', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.77      inference('clc', [status(thm)], ['174', '175'])).
% 0.59/0.77  thf('177', plain, ($false), inference('demod', [status(thm)], ['0', '176'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
