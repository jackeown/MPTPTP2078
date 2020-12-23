%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.usbEmFF5Mq

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:33 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  234 (1573 expanded)
%              Number of leaves         :   23 ( 443 expanded)
%              Depth                    :   31
%              Number of atoms          : 2449 (47264 expanded)
%              Number of equality atoms :   14 (  91 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t39_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ~ ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                        & ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ C @ D ) )
                    & ~ ( ~ ( ( r1_tsep_1 @ B @ D )
                            & ( r1_tsep_1 @ C @ D ) )
                        & ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                    & ~ ( ~ ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                        & ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ D @ C ) )
                    & ~ ( ~ ( ( r1_tsep_1 @ D @ B )
                            & ( r1_tsep_1 @ D @ C ) )
                        & ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) )).

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
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ~ ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                          & ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ C @ D ) )
                      & ~ ( ~ ( ( r1_tsep_1 @ B @ D )
                              & ( r1_tsep_1 @ C @ D ) )
                          & ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                      & ~ ( ~ ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                          & ( r1_tsep_1 @ D @ B )
                          & ( r1_tsep_1 @ D @ C ) )
                      & ~ ( ~ ( ( r1_tsep_1 @ D @ B )
                              & ( r1_tsep_1 @ D @ C ) )
                          & ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

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

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( v1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( X9
       != ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ( ( u1_struct_0 @ X9 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) @ X8 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
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
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
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
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('25',plain,
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['38'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('41',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['30','50'])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57','64'])).

thf('66',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('92',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('103',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('112',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['38'])).

thf('113',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('114',plain,
    ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('116',plain,
    ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['126'])).

thf('128',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('129',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('131',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('132',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['66'])).

thf('134',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('137',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['137'])).

thf('139',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('140',plain,
    ( ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('142',plain,
    ( ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['136','142'])).

thf('144',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('145',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['152'])).

thf('154',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('155',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('157',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('158',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['66'])).

thf('160',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['126'])).

thf('164',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('165',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('167',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('168',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('170',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('171',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('173',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('174',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('176',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ X0 )
        | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('179',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('180',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('188',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('189',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('190',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['188','101','189','125','134','135'])).

thf('191',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['187','190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( r1_tsep_1 @ sk_D @ sk_C )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['137'])).

thf('200',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('201',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('203',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('204',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('206',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['207'])).

thf('209',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['74','101','110','125','134','135','151','160','162','198','206','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.usbEmFF5Mq
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:25:30 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.18/1.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.43  % Solved by: fo/fo7.sh
% 1.18/1.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.43  % done 1177 iterations in 0.955s
% 1.18/1.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.43  % SZS output start Refutation
% 1.18/1.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.18/1.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.18/1.43  thf(sk_D_type, type, sk_D: $i).
% 1.18/1.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.18/1.43  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.18/1.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.18/1.43  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.18/1.43  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.43  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.43  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.18/1.43  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.18/1.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.18/1.43  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.43  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.18/1.43  thf(t39_tmap_1, conjecture,
% 1.18/1.43    (![A:$i]:
% 1.18/1.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.43       ( ![B:$i]:
% 1.18/1.43         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.18/1.43           ( ![C:$i]:
% 1.18/1.43             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.18/1.43               ( ![D:$i]:
% 1.18/1.43                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.18/1.43                   ( ( ~( ( ~( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 1.18/1.43                          ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 1.18/1.43                     ( ~( ( ~( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 1.18/1.43                          ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) ) & 
% 1.18/1.43                     ( ~( ( ~( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.18/1.43                          ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 1.18/1.43                     ( ~( ( ~( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 1.18/1.43                          ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.43  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.43    (~( ![A:$i]:
% 1.18/1.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.18/1.43            ( l1_pre_topc @ A ) ) =>
% 1.18/1.43          ( ![B:$i]:
% 1.18/1.43            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.18/1.43              ( ![C:$i]:
% 1.18/1.43                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.18/1.43                  ( ![D:$i]:
% 1.18/1.43                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.18/1.43                      ( ( ~( ( ~( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 1.18/1.43                             ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 1.18/1.43                        ( ~( ( ~( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 1.18/1.43                             ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) ) & 
% 1.18/1.43                        ( ~( ( ~( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.18/1.43                             ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 1.18/1.43                        ( ~( ( ~( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 1.18/1.43                             ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.18/1.43    inference('cnf.neg', [status(esa)], [t39_tmap_1])).
% 1.18/1.43  thf('0', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf(dt_k1_tsep_1, axiom,
% 1.18/1.43    (![A:$i,B:$i,C:$i]:
% 1.18/1.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.18/1.43         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.18/1.43         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.18/1.43       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.18/1.43         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.18/1.43         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.18/1.43  thf('2', plain,
% 1.18/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X13 @ X14)
% 1.18/1.43          | (v2_struct_0 @ X13)
% 1.18/1.43          | ~ (l1_pre_topc @ X14)
% 1.18/1.43          | (v2_struct_0 @ X14)
% 1.18/1.43          | (v2_struct_0 @ X15)
% 1.18/1.43          | ~ (m1_pre_topc @ X15 @ X14)
% 1.18/1.43          | (v1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X15)))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.18/1.43  thf('3', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.18/1.43          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ X0)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | ~ (l1_pre_topc @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_B))),
% 1.18/1.43      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.43  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('5', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.18/1.43          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ X0)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_B))),
% 1.18/1.43      inference('demod', [status(thm)], ['3', '4'])).
% 1.18/1.43  thf('6', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['0', '5'])).
% 1.18/1.43  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('9', plain,
% 1.18/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X13 @ X14)
% 1.18/1.43          | (v2_struct_0 @ X13)
% 1.18/1.43          | ~ (l1_pre_topc @ X14)
% 1.18/1.43          | (v2_struct_0 @ X14)
% 1.18/1.43          | (v2_struct_0 @ X15)
% 1.18/1.43          | ~ (m1_pre_topc @ X15 @ X14)
% 1.18/1.43          | (m1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X15) @ X14))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.18/1.43  thf('10', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.18/1.43          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ X0)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | ~ (l1_pre_topc @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_B))),
% 1.18/1.43      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.43  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('12', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.18/1.43          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ X0)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_B))),
% 1.18/1.43      inference('demod', [status(thm)], ['10', '11'])).
% 1.18/1.43  thf('13', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.18/1.43      inference('sup-', [status(thm)], ['7', '12'])).
% 1.18/1.43  thf(d2_tsep_1, axiom,
% 1.18/1.43    (![A:$i]:
% 1.18/1.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.43       ( ![B:$i]:
% 1.18/1.43         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.18/1.43           ( ![C:$i]:
% 1.18/1.43             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.18/1.43               ( ![D:$i]:
% 1.18/1.43                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.18/1.43                     ( m1_pre_topc @ D @ A ) ) =>
% 1.18/1.43                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.18/1.43                     ( ( u1_struct_0 @ D ) =
% 1.18/1.43                       ( k2_xboole_0 @
% 1.18/1.43                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.43  thf('14', plain,
% 1.18/1.43      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.43         ((v2_struct_0 @ X7)
% 1.18/1.43          | ~ (m1_pre_topc @ X7 @ X8)
% 1.18/1.43          | (v2_struct_0 @ X9)
% 1.18/1.43          | ~ (v1_pre_topc @ X9)
% 1.18/1.43          | ~ (m1_pre_topc @ X9 @ X8)
% 1.18/1.43          | ((X9) != (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.18/1.43          | ((u1_struct_0 @ X9)
% 1.18/1.43              = (k2_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X10)))
% 1.18/1.43          | ~ (m1_pre_topc @ X10 @ X8)
% 1.18/1.43          | (v2_struct_0 @ X10)
% 1.18/1.43          | ~ (l1_pre_topc @ X8)
% 1.18/1.43          | (v2_struct_0 @ X8))),
% 1.18/1.43      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.18/1.43  thf('15', plain,
% 1.18/1.43      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.18/1.43         ((v2_struct_0 @ X8)
% 1.18/1.43          | ~ (l1_pre_topc @ X8)
% 1.18/1.43          | (v2_struct_0 @ X10)
% 1.18/1.43          | ~ (m1_pre_topc @ X10 @ X8)
% 1.18/1.43          | ((u1_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.18/1.43              = (k2_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X10)))
% 1.18/1.43          | ~ (m1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X10) @ X8)
% 1.18/1.43          | ~ (v1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.18/1.43          | (v2_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.18/1.43          | ~ (m1_pre_topc @ X7 @ X8)
% 1.18/1.43          | (v2_struct_0 @ X7))),
% 1.18/1.43      inference('simplify', [status(thm)], ['14'])).
% 1.18/1.43  thf('16', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | ~ (l1_pre_topc @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_A))),
% 1.18/1.43      inference('sup-', [status(thm)], ['13', '15'])).
% 1.18/1.43  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('20', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A))),
% 1.18/1.43      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 1.18/1.43  thf('21', plain,
% 1.18/1.43      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C))),
% 1.18/1.43      inference('simplify', [status(thm)], ['20'])).
% 1.18/1.43  thf('22', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['6', '21'])).
% 1.18/1.43  thf('23', plain,
% 1.18/1.43      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C))),
% 1.18/1.43      inference('simplify', [status(thm)], ['22'])).
% 1.18/1.43  thf('24', plain,
% 1.18/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X13 @ X14)
% 1.18/1.43          | (v2_struct_0 @ X13)
% 1.18/1.43          | ~ (l1_pre_topc @ X14)
% 1.18/1.43          | (v2_struct_0 @ X14)
% 1.18/1.43          | (v2_struct_0 @ X15)
% 1.18/1.43          | ~ (m1_pre_topc @ X15 @ X14)
% 1.18/1.43          | ~ (v2_struct_0 @ (k1_tsep_1 @ X14 @ X13 @ X15)))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.18/1.43  thf('25', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | ~ (l1_pre_topc @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.18/1.43      inference('sup-', [status(thm)], ['23', '24'])).
% 1.18/1.43  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('29', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B))),
% 1.18/1.43      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 1.18/1.43  thf('30', plain,
% 1.18/1.43      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C))),
% 1.18/1.43      inference('simplify', [status(thm)], ['29'])).
% 1.18/1.43  thf('31', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.18/1.43      inference('sup-', [status(thm)], ['7', '12'])).
% 1.18/1.43  thf(dt_m1_pre_topc, axiom,
% 1.18/1.43    (![A:$i]:
% 1.18/1.43     ( ( l1_pre_topc @ A ) =>
% 1.18/1.43       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.18/1.43  thf('32', plain,
% 1.18/1.43      (![X5 : $i, X6 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.18/1.43  thf('33', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | ~ (l1_pre_topc @ sk_A)
% 1.18/1.43        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['31', '32'])).
% 1.18/1.43  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('35', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_C)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('demod', [status(thm)], ['33', '34'])).
% 1.18/1.43  thf(dt_l1_pre_topc, axiom,
% 1.18/1.43    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.18/1.43  thf('36', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.43  thf('37', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.43  thf('38', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('39', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('split', [status(esa)], ['38'])).
% 1.18/1.43  thf(d3_tsep_1, axiom,
% 1.18/1.43    (![A:$i]:
% 1.18/1.43     ( ( l1_struct_0 @ A ) =>
% 1.18/1.43       ( ![B:$i]:
% 1.18/1.43         ( ( l1_struct_0 @ B ) =>
% 1.18/1.43           ( ( r1_tsep_1 @ A @ B ) <=>
% 1.18/1.43             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.18/1.43  thf('40', plain,
% 1.18/1.43      (![X11 : $i, X12 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X11)
% 1.18/1.43          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.18/1.43          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.18/1.43          | ~ (l1_struct_0 @ X12))),
% 1.18/1.43      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.18/1.43  thf('41', plain,
% 1.18/1.43      (((~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.18/1.43         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.43  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('43', plain,
% 1.18/1.43      (![X5 : $i, X6 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.18/1.43  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.18/1.43      inference('sup-', [status(thm)], ['42', '43'])).
% 1.18/1.43  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.43      inference('demod', [status(thm)], ['44', '45'])).
% 1.18/1.43  thf('47', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.43  thf('48', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('49', plain,
% 1.18/1.43      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.18/1.43         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('demod', [status(thm)], ['41', '48'])).
% 1.18/1.43  thf('50', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['37', '49'])).
% 1.18/1.43  thf('51', plain,
% 1.18/1.43      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43          (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup+', [status(thm)], ['30', '50'])).
% 1.18/1.43  thf('52', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43            (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('simplify', [status(thm)], ['51'])).
% 1.18/1.43  thf(t70_xboole_1, axiom,
% 1.18/1.43    (![A:$i,B:$i,C:$i]:
% 1.18/1.43     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.18/1.43            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.18/1.43       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.18/1.43            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.18/1.43  thf('53', plain,
% 1.18/1.43      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.18/1.43         ((r1_xboole_0 @ X0 @ X3)
% 1.18/1.43          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 1.18/1.43      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.18/1.43  thf('54', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['52', '53'])).
% 1.18/1.43  thf('55', plain,
% 1.18/1.43      (![X11 : $i, X12 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X11)
% 1.18/1.43          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.18/1.43          | (r1_tsep_1 @ X12 @ X11)
% 1.18/1.43          | ~ (l1_struct_0 @ X12))),
% 1.18/1.43      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.18/1.43  thf('56', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ sk_C)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['54', '55'])).
% 1.18/1.43  thf('57', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('59', plain,
% 1.18/1.43      (![X5 : $i, X6 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.18/1.43  thf('60', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.18/1.43      inference('sup-', [status(thm)], ['58', '59'])).
% 1.18/1.43  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.43      inference('demod', [status(thm)], ['60', '61'])).
% 1.18/1.43  thf('63', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.43  thf('64', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.43      inference('sup-', [status(thm)], ['62', '63'])).
% 1.18/1.43  thf('65', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('demod', [status(thm)], ['56', '57', '64'])).
% 1.18/1.43  thf('66', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ sk_C))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('67', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_D @ sk_C)) <= (~ ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('68', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['65', '67'])).
% 1.18/1.43  thf('69', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('70', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['68', '69'])).
% 1.18/1.43  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('72', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_A))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ sk_C)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['70', '71'])).
% 1.18/1.43  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('74', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.18/1.43       ((r1_tsep_1 @ sk_D @ sk_C))),
% 1.18/1.43      inference('sup-', [status(thm)], ['72', '73'])).
% 1.18/1.43  thf('75', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43            (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('simplify', [status(thm)], ['51'])).
% 1.18/1.43  thf('76', plain,
% 1.18/1.43      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.18/1.43         ((r1_xboole_0 @ X0 @ X1)
% 1.18/1.43          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 1.18/1.43      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.18/1.43  thf('77', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['75', '76'])).
% 1.18/1.43  thf('78', plain,
% 1.18/1.43      (![X11 : $i, X12 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X11)
% 1.18/1.43          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.18/1.43          | (r1_tsep_1 @ X12 @ X11)
% 1.18/1.43          | ~ (l1_struct_0 @ X12))),
% 1.18/1.43      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.18/1.43  thf('79', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_B)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['77', '78'])).
% 1.18/1.43  thf('80', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('82', plain,
% 1.18/1.43      (![X5 : $i, X6 : $i]:
% 1.18/1.43         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.18/1.43  thf('83', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.18/1.43      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.43  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.43      inference('demod', [status(thm)], ['83', '84'])).
% 1.18/1.43  thf('86', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.18/1.43      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.43  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.43      inference('sup-', [status(thm)], ['85', '86'])).
% 1.18/1.43  thf('88', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ sk_B)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('demod', [status(thm)], ['79', '80', '87'])).
% 1.18/1.43  thf(symmetry_r1_tsep_1, axiom,
% 1.18/1.43    (![A:$i,B:$i]:
% 1.18/1.43     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 1.18/1.43       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 1.18/1.43  thf('89', plain,
% 1.18/1.43      (![X16 : $i, X17 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X16)
% 1.18/1.43          | ~ (l1_struct_0 @ X17)
% 1.18/1.43          | (r1_tsep_1 @ X17 @ X16)
% 1.18/1.43          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.18/1.43      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.18/1.43  thf('90', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_tsep_1 @ sk_B @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_B)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['88', '89'])).
% 1.18/1.43  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.43      inference('sup-', [status(thm)], ['85', '86'])).
% 1.18/1.43  thf('92', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('93', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_tsep_1 @ sk_B @ sk_D)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.18/1.43  thf('94', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('95', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['93', '94'])).
% 1.18/1.43  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('97', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['95', '96'])).
% 1.18/1.43  thf('98', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('99', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_A))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['97', '98'])).
% 1.18/1.43  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('101', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_B @ sk_D)) | 
% 1.18/1.43       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['99', '100'])).
% 1.18/1.43  thf('102', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_C)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ sk_B)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('demod', [status(thm)], ['79', '80', '87'])).
% 1.18/1.43  thf('103', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('104', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['102', '103'])).
% 1.18/1.43  thf('105', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('106', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['104', '105'])).
% 1.18/1.43  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('108', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_A))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['106', '107'])).
% 1.18/1.43  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('110', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.18/1.43       ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.18/1.43      inference('sup-', [status(thm)], ['108', '109'])).
% 1.18/1.43  thf('111', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.43  thf('112', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('split', [status(esa)], ['38'])).
% 1.18/1.43  thf('113', plain,
% 1.18/1.43      (![X16 : $i, X17 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X16)
% 1.18/1.43          | ~ (l1_struct_0 @ X17)
% 1.18/1.43          | (r1_tsep_1 @ X17 @ X16)
% 1.18/1.43          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.18/1.43      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.18/1.43  thf('114', plain,
% 1.18/1.43      ((((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['112', '113'])).
% 1.18/1.43  thf('115', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('116', plain,
% 1.18/1.43      ((((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('demod', [status(thm)], ['114', '115'])).
% 1.18/1.43  thf('117', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['111', '116'])).
% 1.18/1.43  thf('118', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('119', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['117', '118'])).
% 1.18/1.43  thf('120', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('121', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['119', '120'])).
% 1.18/1.43  thf('122', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('123', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_A))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.18/1.43             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('clc', [status(thm)], ['121', '122'])).
% 1.18/1.43  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('125', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.18/1.43       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.18/1.43      inference('sup-', [status(thm)], ['123', '124'])).
% 1.18/1.43  thf('126', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ sk_C)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('127', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('split', [status(esa)], ['126'])).
% 1.18/1.43  thf('128', plain,
% 1.18/1.43      (![X16 : $i, X17 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X16)
% 1.18/1.43          | ~ (l1_struct_0 @ X17)
% 1.18/1.43          | (r1_tsep_1 @ X17 @ X16)
% 1.18/1.43          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.18/1.43      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.18/1.43  thf('129', plain,
% 1.18/1.43      ((((r1_tsep_1 @ sk_C @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_C)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['127', '128'])).
% 1.18/1.43  thf('130', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.43      inference('sup-', [status(thm)], ['62', '63'])).
% 1.18/1.43  thf('131', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('132', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.18/1.43  thf('133', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_C @ sk_D)) <= (~ ((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('134', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_C @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 1.18/1.43      inference('sup-', [status(thm)], ['132', '133'])).
% 1.18/1.43  thf('135', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.18/1.43       ~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C)) | 
% 1.18/1.43       ~ ((r1_tsep_1 @ sk_C @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 1.18/1.43       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('136', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.43  thf('137', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_B @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ sk_C))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('138', plain,
% 1.18/1.43      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 1.18/1.43         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('split', [status(esa)], ['137'])).
% 1.18/1.43  thf('139', plain,
% 1.18/1.43      (![X16 : $i, X17 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X16)
% 1.18/1.43          | ~ (l1_struct_0 @ X17)
% 1.18/1.43          | (r1_tsep_1 @ X17 @ X16)
% 1.18/1.43          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.18/1.43      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.18/1.43  thf('140', plain,
% 1.18/1.43      ((((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['138', '139'])).
% 1.18/1.43  thf('141', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('142', plain,
% 1.18/1.43      ((((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('demod', [status(thm)], ['140', '141'])).
% 1.18/1.43  thf('143', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['136', '142'])).
% 1.18/1.43  thf('144', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('145', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.18/1.43             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['143', '144'])).
% 1.18/1.43  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('147', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.18/1.43             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('clc', [status(thm)], ['145', '146'])).
% 1.18/1.43  thf('148', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('149', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_A))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.18/1.43             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.18/1.43      inference('clc', [status(thm)], ['147', '148'])).
% 1.18/1.43  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('151', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.18/1.43       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['149', '150'])).
% 1.18/1.43  thf('152', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_C @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43        | ~ (r1_tsep_1 @ sk_D @ sk_C))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('153', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.18/1.43      inference('split', [status(esa)], ['152'])).
% 1.18/1.43  thf('154', plain,
% 1.18/1.43      (![X16 : $i, X17 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X16)
% 1.18/1.43          | ~ (l1_struct_0 @ X17)
% 1.18/1.43          | (r1_tsep_1 @ X17 @ X16)
% 1.18/1.43          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.18/1.43      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.18/1.43  thf('155', plain,
% 1.18/1.43      ((((r1_tsep_1 @ sk_D @ sk_C)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['153', '154'])).
% 1.18/1.43  thf('156', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('157', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.43      inference('sup-', [status(thm)], ['62', '63'])).
% 1.18/1.43  thf('158', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.18/1.43      inference('demod', [status(thm)], ['155', '156', '157'])).
% 1.18/1.43  thf('159', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_D @ sk_C)) <= (~ ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('160', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_C)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 1.18/1.43      inference('sup-', [status(thm)], ['158', '159'])).
% 1.18/1.43  thf('161', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_C @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ sk_C)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('162', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C)) | 
% 1.18/1.43       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.18/1.43       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.18/1.43      inference('split', [status(esa)], ['161'])).
% 1.18/1.43  thf('163', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('split', [status(esa)], ['126'])).
% 1.18/1.43  thf('164', plain,
% 1.18/1.43      (![X11 : $i, X12 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X11)
% 1.18/1.43          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.18/1.43          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.18/1.43          | ~ (l1_struct_0 @ X12))),
% 1.18/1.43      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.18/1.43  thf('165', plain,
% 1.18/1.43      (((~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 1.18/1.43         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['163', '164'])).
% 1.18/1.43  thf('166', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('167', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.43      inference('sup-', [status(thm)], ['62', '63'])).
% 1.18/1.43  thf('168', plain,
% 1.18/1.43      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.18/1.43      inference('demod', [status(thm)], ['165', '166', '167'])).
% 1.18/1.43  thf('169', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('split', [status(esa)], ['38'])).
% 1.18/1.43  thf('170', plain,
% 1.18/1.43      (![X11 : $i, X12 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X11)
% 1.18/1.43          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.18/1.43          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.18/1.43          | ~ (l1_struct_0 @ X12))),
% 1.18/1.43      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.18/1.43  thf('171', plain,
% 1.18/1.43      (((~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.18/1.43         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['169', '170'])).
% 1.18/1.43  thf('172', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('173', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.43      inference('sup-', [status(thm)], ['85', '86'])).
% 1.18/1.43  thf('174', plain,
% 1.18/1.43      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('demod', [status(thm)], ['171', '172', '173'])).
% 1.18/1.43  thf('175', plain,
% 1.18/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.43         ((r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 1.18/1.43          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.18/1.43          | ~ (r1_xboole_0 @ X0 @ X2))),
% 1.18/1.43      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.18/1.43  thf('176', plain,
% 1.18/1.43      ((![X0 : $i]:
% 1.18/1.43          (~ (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ X0)
% 1.18/1.43           | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43              (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['174', '175'])).
% 1.18/1.43  thf('177', plain,
% 1.18/1.43      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.43         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)) & ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['168', '176'])).
% 1.18/1.43  thf('178', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C)
% 1.18/1.43        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.43  thf('179', plain,
% 1.18/1.43      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43        | (v2_struct_0 @ sk_B)
% 1.18/1.43        | (v2_struct_0 @ sk_A)
% 1.18/1.43        | (v2_struct_0 @ sk_C))),
% 1.18/1.43      inference('simplify', [status(thm)], ['29'])).
% 1.18/1.43  thf('180', plain,
% 1.18/1.43      (![X11 : $i, X12 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X11)
% 1.18/1.43          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.18/1.43          | (r1_tsep_1 @ X12 @ X11)
% 1.18/1.43          | ~ (l1_struct_0 @ X12))),
% 1.18/1.43      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.18/1.43  thf('181', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 1.18/1.43             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43          | (v2_struct_0 @ sk_C)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_B)
% 1.18/1.43          | ~ (l1_struct_0 @ X0)
% 1.18/1.43          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['179', '180'])).
% 1.18/1.43  thf('182', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         ((v2_struct_0 @ sk_C)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_B)
% 1.18/1.43          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          | ~ (l1_struct_0 @ X0)
% 1.18/1.43          | (v2_struct_0 @ sk_B)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_C)
% 1.18/1.43          | ~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 1.18/1.43               (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.18/1.43      inference('sup-', [status(thm)], ['178', '181'])).
% 1.18/1.43  thf('183', plain,
% 1.18/1.43      (![X0 : $i]:
% 1.18/1.43         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 1.18/1.43             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.18/1.43          | ~ (l1_struct_0 @ X0)
% 1.18/1.43          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43          | (v2_struct_0 @ sk_B)
% 1.18/1.43          | (v2_struct_0 @ sk_A)
% 1.18/1.43          | (v2_struct_0 @ sk_C))),
% 1.18/1.43      inference('simplify', [status(thm)], ['182'])).
% 1.18/1.43  thf('184', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)) & ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['177', '183'])).
% 1.18/1.43  thf('185', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('186', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C)
% 1.18/1.43         | (v2_struct_0 @ sk_A)
% 1.18/1.43         | (v2_struct_0 @ sk_B)
% 1.18/1.43         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)) & ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('demod', [status(thm)], ['184', '185'])).
% 1.18/1.43  thf('187', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.18/1.43         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('188', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_C)) | 
% 1.18/1.43       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['72', '73'])).
% 1.18/1.43  thf('189', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_B)) | 
% 1.18/1.43       ~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['108', '109'])).
% 1.18/1.43  thf('190', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('sat_resolution*', [status(thm)],
% 1.18/1.43                ['188', '101', '189', '125', '134', '135'])).
% 1.18/1.43  thf('191', plain, (~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 1.18/1.43      inference('simpl_trail', [status(thm)], ['187', '190'])).
% 1.18/1.43  thf('192', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)) & ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['186', '191'])).
% 1.18/1.43  thf('193', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('194', plain,
% 1.18/1.43      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)) & ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('clc', [status(thm)], ['192', '193'])).
% 1.18/1.43  thf('195', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('196', plain,
% 1.18/1.43      (((v2_struct_0 @ sk_A))
% 1.18/1.43         <= (((r1_tsep_1 @ sk_D @ sk_C)) & ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('clc', [status(thm)], ['194', '195'])).
% 1.18/1.43  thf('197', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('198', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 1.18/1.43      inference('sup-', [status(thm)], ['196', '197'])).
% 1.18/1.43  thf('199', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.18/1.43      inference('split', [status(esa)], ['137'])).
% 1.18/1.43  thf('200', plain,
% 1.18/1.43      (![X16 : $i, X17 : $i]:
% 1.18/1.43         (~ (l1_struct_0 @ X16)
% 1.18/1.43          | ~ (l1_struct_0 @ X17)
% 1.18/1.43          | (r1_tsep_1 @ X17 @ X16)
% 1.18/1.43          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.18/1.43      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.18/1.43  thf('201', plain,
% 1.18/1.43      ((((r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_D)
% 1.18/1.43         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.18/1.43      inference('sup-', [status(thm)], ['199', '200'])).
% 1.18/1.43  thf('202', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.18/1.43  thf('203', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.43      inference('sup-', [status(thm)], ['85', '86'])).
% 1.18/1.43  thf('204', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.18/1.43      inference('demod', [status(thm)], ['201', '202', '203'])).
% 1.18/1.43  thf('205', plain,
% 1.18/1.43      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.18/1.43      inference('split', [status(esa)], ['66'])).
% 1.18/1.43  thf('206', plain,
% 1.18/1.43      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.18/1.43      inference('sup-', [status(thm)], ['204', '205'])).
% 1.18/1.43  thf('207', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_B @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ sk_B)
% 1.18/1.43        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.18/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.43  thf('208', plain,
% 1.18/1.43      (((r1_tsep_1 @ sk_B @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 1.18/1.43       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.18/1.43       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.18/1.43      inference('split', [status(esa)], ['207'])).
% 1.18/1.43  thf('209', plain, ($false),
% 1.18/1.43      inference('sat_resolution*', [status(thm)],
% 1.18/1.43                ['74', '101', '110', '125', '134', '135', '151', '160', '162', 
% 1.18/1.43                 '198', '206', '208'])).
% 1.18/1.43  
% 1.18/1.43  % SZS output end Refutation
% 1.18/1.43  
% 1.18/1.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
