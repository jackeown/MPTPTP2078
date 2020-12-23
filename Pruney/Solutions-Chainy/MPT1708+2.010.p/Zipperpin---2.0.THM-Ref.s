%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pPkWFpKqeK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:14 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 428 expanded)
%              Number of leaves         :   28 ( 128 expanded)
%              Depth                    :   36
%              Number of atoms          : 1606 (9421 expanded)
%              Number of equality atoms :   40 ( 357 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X21 @ X20 @ X22 ) @ X21 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X21 @ X20 @ X22 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( r1_tsep_1 @ X16 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( X19
       != ( k2_tsep_1 @ X17 @ X16 @ X18 ) )
      | ( ( u1_struct_0 @ X19 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X17 @ X16 @ X18 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X17 @ X16 @ X18 ) @ X17 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X17 @ X16 @ X18 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X17 @ X16 @ X18 ) )
      | ( r1_tsep_1 @ X16 @ X18 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X21 @ X20 @ X22 ) ) ) ),
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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

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
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X21 @ X20 @ X22 ) ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X21 @ X20 @ X22 ) ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) )
      | ( X23 != sk_D_1 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_C ) )
      | ( X24 != sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X24: $i] :
        ( ( X24 != sk_D_1 )
        | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X24: $i] :
        ( ( X24 != sk_D_1 )
        | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X24: $i] :
        ( ( X24 != sk_D_1 )
        | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_C ) ) ) ),
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
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ~ ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X24: $i] :
        ( ( X24 != sk_D_1 )
        | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_C ) ) )
    | ! [X23: $i] :
        ( ( X23 != sk_D_1 )
        | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('102',plain,(
    ! [X24: $i] :
      ( ( X24 != sk_D_1 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['86','102'])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','103'])).

thf('105',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pPkWFpKqeK
% 0.17/0.36  % Computer   : n010.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 15:32:15 EST 2020
% 0.17/0.36  % CPUTime    : 
% 0.17/0.36  % Running portfolio for 600 s
% 0.17/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 386 iterations in 0.194s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.45/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(t17_tmap_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.45/0.63                 ( ![D:$i]:
% 0.45/0.63                   ( ( m1_subset_1 @
% 0.45/0.63                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.45/0.63                     ( ( ?[E:$i]:
% 0.45/0.63                         ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.63                       ( ?[E:$i]:
% 0.45/0.63                         ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.63            ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.63              ( ![C:$i]:
% 0.45/0.63                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.45/0.63                    ( ![D:$i]:
% 0.45/0.63                      ( ( m1_subset_1 @
% 0.45/0.63                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.45/0.63                        ( ( ?[E:$i]:
% 0.45/0.63                            ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.63                          ( ?[E:$i]:
% 0.45/0.63                            ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 0.45/0.63  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k2_tsep_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.45/0.63         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.45/0.63         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 0.45/0.63         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.45/0.63         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.63          | (m1_pre_topc @ (k2_tsep_1 @ X21 @ X20 @ X22) @ X21))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.63  thf(dt_m1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X13 @ X14)
% 0.45/0.63          | (l1_pre_topc @ X13)
% 0.45/0.63          | ~ (l1_pre_topc @ X14))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf(dt_l1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.63          | (v1_pre_topc @ (k2_tsep_1 @ X21 @ X20 @ X22)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['15', '20'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.63  thf(d5_tsep_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.45/0.63                 ( ![D:$i]:
% 0.45/0.63                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.45/0.63                       ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.63                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 0.45/0.63                       ( ( u1_struct_0 @ D ) =
% 0.45/0.63                         ( k3_xboole_0 @
% 0.45/0.63                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X16)
% 0.45/0.63          | ~ (m1_pre_topc @ X16 @ X17)
% 0.45/0.63          | (r1_tsep_1 @ X16 @ X18)
% 0.45/0.63          | (v2_struct_0 @ X19)
% 0.45/0.63          | ~ (v1_pre_topc @ X19)
% 0.45/0.63          | ~ (m1_pre_topc @ X19 @ X17)
% 0.45/0.63          | ((X19) != (k2_tsep_1 @ X17 @ X16 @ X18))
% 0.45/0.63          | ((u1_struct_0 @ X19)
% 0.45/0.63              = (k3_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18)))
% 0.45/0.63          | ~ (m1_pre_topc @ X18 @ X17)
% 0.45/0.63          | (v2_struct_0 @ X18)
% 0.45/0.63          | ~ (l1_pre_topc @ X17)
% 0.45/0.63          | (v2_struct_0 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_tsep_1])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X17)
% 0.45/0.63          | ~ (l1_pre_topc @ X17)
% 0.45/0.63          | (v2_struct_0 @ X18)
% 0.45/0.63          | ~ (m1_pre_topc @ X18 @ X17)
% 0.45/0.63          | ((u1_struct_0 @ (k2_tsep_1 @ X17 @ X16 @ X18))
% 0.45/0.63              = (k3_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18)))
% 0.45/0.63          | ~ (m1_pre_topc @ (k2_tsep_1 @ X17 @ X16 @ X18) @ X17)
% 0.45/0.63          | ~ (v1_pre_topc @ (k2_tsep_1 @ X17 @ X16 @ X18))
% 0.45/0.63          | (v2_struct_0 @ (k2_tsep_1 @ X17 @ X16 @ X18))
% 0.45/0.63          | (r1_tsep_1 @ X16 @ X18)
% 0.45/0.63          | ~ (m1_pre_topc @ X16 @ X17)
% 0.45/0.63          | (v2_struct_0 @ X16))),
% 0.45/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '24'])).
% 0.45/0.63  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.63          | ~ (v2_struct_0 @ (k2_tsep_1 @ X21 @ X20 @ X22)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t2_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         ((r2_hidden @ X10 @ X11)
% 0.45/0.63          | (v1_xboole_0 @ X11)
% 0.45/0.63          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ 
% 0.45/0.63           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ 
% 0.45/0.63         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['39', '42'])).
% 0.45/0.63  thf(t48_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.63           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf(d5_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.45/0.63       ( ![D:$i]:
% 0.45/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X4 @ X3)
% 0.45/0.63          | (r2_hidden @ X4 @ X1)
% 0.45/0.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.63         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['44', '46'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['43', '47'])).
% 0.45/0.63  thf(fc2_struct_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.63       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (![X15 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.45/0.63          | ~ (l1_struct_0 @ X15)
% 0.45/0.63          | (v2_struct_0 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '50'])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.63          | ~ (v2_struct_0 @ (k2_tsep_1 @ X21 @ X20 @ X22)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.63  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['58'])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | (r2_hidden @ X0 @ X3)
% 0.45/0.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.63      inference('simplify', [status(thm)], ['60'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_C)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B)
% 0.45/0.63          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63          | (r2_hidden @ sk_D_1 @ X0)
% 0.45/0.63          | (r2_hidden @ sk_D_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['59', '61'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ 
% 0.45/0.63         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['39', '42'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.63           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X4 @ X3)
% 0.45/0.63          | ~ (r2_hidden @ X4 @ X2)
% 0.45/0.63          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X4 @ X2)
% 0.45/0.63          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.63          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['64', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | ~ (r2_hidden @ sk_D_1 @ 
% 0.45/0.63             (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['63', '67'])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['62', '68'])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['69'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      (![X15 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.45/0.63          | ~ (l1_struct_0 @ X15)
% 0.45/0.63          | (v2_struct_0 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['70', '71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '72'])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['73'])).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.63          | ~ (v2_struct_0 @ (k2_tsep_1 @ X21 @ X20 @ X22)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.63  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('79', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('80', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['80'])).
% 0.45/0.63  thf(t1_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      (![X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B))
% 0.45/0.63          | ((X23) != (sk_D_1))
% 0.45/0.63          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_C))
% 0.45/0.63          | ((X24) != (sk_D_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      ((![X24 : $i]:
% 0.45/0.63          (((X24) != (sk_D_1)) | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_C))))
% 0.45/0.63         <= ((![X24 : $i]:
% 0.45/0.63                (((X24) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('split', [status(esa)], ['84'])).
% 0.45/0.63  thf('86', plain,
% 0.45/0.63      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.45/0.63         <= ((![X24 : $i]:
% 0.45/0.63                (((X24) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['85'])).
% 0.45/0.63  thf('87', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['58'])).
% 0.45/0.63  thf('88', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.63  thf('89', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.63  thf('90', plain,
% 0.45/0.63      ((![X23 : $i]:
% 0.45/0.63          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B))))
% 0.45/0.63         <= ((![X23 : $i]:
% 0.45/0.63                (((X23) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('split', [status(esa)], ['84'])).
% 0.45/0.63  thf('91', plain,
% 0.45/0.63      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.45/0.63         <= ((![X23 : $i]:
% 0.45/0.63                (((X23) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['90'])).
% 0.45/0.63  thf('92', plain,
% 0.45/0.63      ((((r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63         | (v2_struct_0 @ sk_B)
% 0.45/0.63         | (v2_struct_0 @ sk_A)
% 0.45/0.63         | (v2_struct_0 @ sk_C)))
% 0.45/0.63         <= ((![X23 : $i]:
% 0.45/0.63                (((X23) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['89', '91'])).
% 0.45/0.63  thf('93', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('94', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.45/0.63         <= ((![X23 : $i]:
% 0.45/0.63                (((X23) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.63  thf('95', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('96', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= ((![X23 : $i]:
% 0.45/0.63                (((X23) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('clc', [status(thm)], ['94', '95'])).
% 0.45/0.63  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('98', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A))
% 0.45/0.63         <= ((![X23 : $i]:
% 0.45/0.63                (((X23) != (sk_D_1))
% 0.45/0.63                 | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('clc', [status(thm)], ['96', '97'])).
% 0.45/0.63  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('100', plain,
% 0.45/0.63      (~
% 0.45/0.63       (![X23 : $i]:
% 0.45/0.63          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.63  thf('101', plain,
% 0.45/0.63      ((![X24 : $i]:
% 0.45/0.63          (((X24) != (sk_D_1)) | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_C)))) | 
% 0.45/0.63       (![X23 : $i]:
% 0.45/0.63          (((X23) != (sk_D_1)) | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('split', [status(esa)], ['84'])).
% 0.45/0.63  thf('102', plain,
% 0.45/0.63      ((![X24 : $i]:
% 0.45/0.63          (((X24) != (sk_D_1)) | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_C))))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['100', '101'])).
% 0.45/0.63  thf('103', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['86', '102'])).
% 0.45/0.63  thf('104', plain,
% 0.45/0.63      (((r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['83', '103'])).
% 0.45/0.63  thf('105', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('106', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['104', '105'])).
% 0.45/0.63  thf('107', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('108', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('clc', [status(thm)], ['106', '107'])).
% 0.45/0.63  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('110', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('clc', [status(thm)], ['108', '109'])).
% 0.45/0.63  thf('111', plain, ($false), inference('demod', [status(thm)], ['0', '110'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
