%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2BWMy6epcu

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:30 EST 2020

% Result     : Theorem 4.37s
% Output     : Refutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 465 expanded)
%              Number of leaves         :   26 ( 139 expanded)
%              Depth                    :   29
%              Number of atoms          : 1669 (9942 expanded)
%              Number of equality atoms :   31 (  76 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t30_tmap_1,conjecture,(
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
                 => ( ( ( m1_pre_topc @ B @ D )
                      & ( m1_pre_topc @ C @ D ) )
                   => ( ( r1_tsep_1 @ B @ C )
                      | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) )).

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
                   => ( ( ( m1_pre_topc @ B @ D )
                        & ( m1_pre_topc @ C @ D ) )
                     => ( ( r1_tsep_1 @ B @ C )
                        | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
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

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tmap_1,axiom,(
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
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ B @ D )
                          & ( m1_pre_topc @ C @ E ) )
                       => ( ( r1_tsep_1 @ B @ C )
                          | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( r1_tsep_1 @ X16 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X17 @ X16 @ X19 ) @ ( k2_tsep_1 @ X17 @ X18 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X17 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_tmap_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k2_tsep_1 @ sk_A @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k2_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( k2_tsep_1 @ X15 @ X14 @ X14 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_tmap_1])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k1_tsep_1 @ X13 @ X12 @ X12 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['25','26','27','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X23 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('65',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

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

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( X7
       != ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ( ( u1_struct_0 @ X7 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('83',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('86',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','83','87','88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('93',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('94',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    = ( u1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['51','108','109'])).

thf('111',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) )
      | ( m1_pre_topc @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['0','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2BWMy6epcu
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.37/4.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.37/4.61  % Solved by: fo/fo7.sh
% 4.37/4.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.37/4.61  % done 1815 iterations in 4.127s
% 4.37/4.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.37/4.61  % SZS output start Refutation
% 4.37/4.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.37/4.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.37/4.61  thf(sk_C_type, type, sk_C: $i).
% 4.37/4.61  thf(sk_A_type, type, sk_A: $i).
% 4.37/4.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.37/4.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.37/4.61  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 4.37/4.61  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 4.37/4.61  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 4.37/4.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.37/4.61  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 4.37/4.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 4.37/4.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 4.37/4.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.37/4.61  thf(sk_B_type, type, sk_B: $i).
% 4.37/4.61  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 4.37/4.61  thf(sk_D_type, type, sk_D: $i).
% 4.37/4.61  thf(t30_tmap_1, conjecture,
% 4.37/4.61    (![A:$i]:
% 4.37/4.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.37/4.61       ( ![B:$i]:
% 4.37/4.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.37/4.61           ( ![C:$i]:
% 4.37/4.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 4.37/4.61               ( ![D:$i]:
% 4.37/4.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 4.37/4.61                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 4.37/4.61                     ( ( r1_tsep_1 @ B @ C ) | 
% 4.37/4.61                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 4.37/4.61  thf(zf_stmt_0, negated_conjecture,
% 4.37/4.61    (~( ![A:$i]:
% 4.37/4.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.37/4.61            ( l1_pre_topc @ A ) ) =>
% 4.37/4.61          ( ![B:$i]:
% 4.37/4.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.37/4.61              ( ![C:$i]:
% 4.37/4.61                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 4.37/4.61                  ( ![D:$i]:
% 4.37/4.61                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 4.37/4.61                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 4.37/4.61                        ( ( r1_tsep_1 @ B @ C ) | 
% 4.37/4.61                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 4.37/4.61    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 4.37/4.61  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf(dt_k2_tsep_1, axiom,
% 4.37/4.61    (![A:$i,B:$i,C:$i]:
% 4.37/4.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 4.37/4.61         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 4.37/4.61         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 4.37/4.61       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 4.37/4.61         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 4.37/4.61         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 4.37/4.61  thf('3', plain,
% 4.37/4.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.37/4.61         (~ (m1_pre_topc @ X9 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X9)
% 4.37/4.61          | ~ (l1_pre_topc @ X10)
% 4.37/4.61          | (v2_struct_0 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X11)
% 4.37/4.61          | ~ (m1_pre_topc @ X11 @ X10)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 4.37/4.61      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 4.37/4.61  thf('4', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('sup-', [status(thm)], ['2', '3'])).
% 4.37/4.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('6', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('demod', [status(thm)], ['4', '5'])).
% 4.37/4.61  thf('7', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['1', '6'])).
% 4.37/4.61  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf(t28_tmap_1, axiom,
% 4.37/4.61    (![A:$i]:
% 4.37/4.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.37/4.61       ( ![B:$i]:
% 4.37/4.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.37/4.61           ( ![C:$i]:
% 4.37/4.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 4.37/4.61               ( ![D:$i]:
% 4.37/4.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 4.37/4.61                   ( ![E:$i]:
% 4.37/4.61                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 4.37/4.61                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 4.37/4.61                         ( ( r1_tsep_1 @ B @ C ) | 
% 4.37/4.61                           ( m1_pre_topc @
% 4.37/4.61                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 4.37/4.61                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.37/4.61  thf('12', plain,
% 4.37/4.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 4.37/4.61         ((v2_struct_0 @ X16)
% 4.37/4.61          | ~ (m1_pre_topc @ X16 @ X17)
% 4.37/4.61          | (v2_struct_0 @ X18)
% 4.37/4.61          | ~ (m1_pre_topc @ X18 @ X17)
% 4.37/4.61          | ~ (m1_pre_topc @ X16 @ X18)
% 4.37/4.61          | (r1_tsep_1 @ X16 @ X19)
% 4.37/4.61          | ~ (m1_pre_topc @ X19 @ X20)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ X17 @ X16 @ X19) @ 
% 4.37/4.61             (k2_tsep_1 @ X17 @ X18 @ X20))
% 4.37/4.61          | ~ (m1_pre_topc @ X20 @ X17)
% 4.37/4.61          | (v2_struct_0 @ X20)
% 4.37/4.61          | ~ (m1_pre_topc @ X19 @ X17)
% 4.37/4.61          | (v2_struct_0 @ X19)
% 4.37/4.61          | ~ (l1_pre_topc @ X17)
% 4.37/4.61          | ~ (v2_pre_topc @ X17)
% 4.37/4.61          | (v2_struct_0 @ X17))),
% 4.37/4.61      inference('cnf', [status(esa)], [t28_tmap_1])).
% 4.37/4.61  thf('13', plain,
% 4.37/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_A)
% 4.37/4.61          | ~ (v2_pre_topc @ sk_A)
% 4.37/4.61          | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X1)
% 4.37/4.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 4.37/4.61             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ X1)
% 4.37/4.61          | (r1_tsep_1 @ sk_B @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ sk_B @ X2)
% 4.37/4.61          | ~ (m1_pre_topc @ X2 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X2)
% 4.37/4.61          | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('sup-', [status(thm)], ['11', '12'])).
% 4.37/4.61  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('16', plain,
% 4.37/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X1)
% 4.37/4.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 4.37/4.61             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ X1)
% 4.37/4.61          | (r1_tsep_1 @ sk_B @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ sk_B @ X2)
% 4.37/4.61          | ~ (m1_pre_topc @ X2 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X2)
% 4.37/4.61          | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('demod', [status(thm)], ['13', '14', '15'])).
% 4.37/4.61  thf('17', plain,
% 4.37/4.61      (![X0 : $i, X1 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_B)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.37/4.61          | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61          | ~ (m1_pre_topc @ sk_C @ X1)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.37/4.61             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 4.37/4.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X1)
% 4.37/4.61          | (v2_struct_0 @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['10', '16'])).
% 4.37/4.61  thf('18', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.37/4.61             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 4.37/4.61          | ~ (m1_pre_topc @ sk_C @ X0)
% 4.37/4.61          | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 4.37/4.61          | (v2_struct_0 @ sk_D)
% 4.37/4.61          | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('sup-', [status(thm)], ['9', '17'])).
% 4.37/4.61  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('20', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.37/4.61             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 4.37/4.61          | ~ (m1_pre_topc @ sk_C @ X0)
% 4.37/4.61          | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ sk_D)
% 4.37/4.61          | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('demod', [status(thm)], ['18', '19'])).
% 4.37/4.61  thf('21', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.37/4.61           (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['8', '20'])).
% 4.37/4.61  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('23', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf(t26_tmap_1, axiom,
% 4.37/4.61    (![A:$i]:
% 4.37/4.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.37/4.61       ( ![B:$i]:
% 4.37/4.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.37/4.61           ( ( k2_tsep_1 @ A @ B @ B ) =
% 4.37/4.61             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 4.37/4.61  thf('24', plain,
% 4.37/4.61      (![X14 : $i, X15 : $i]:
% 4.37/4.61         ((v2_struct_0 @ X14)
% 4.37/4.61          | ~ (m1_pre_topc @ X14 @ X15)
% 4.37/4.61          | ((k2_tsep_1 @ X15 @ X14 @ X14)
% 4.37/4.61              = (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 4.37/4.61          | ~ (l1_pre_topc @ X15)
% 4.37/4.61          | ~ (v2_pre_topc @ X15)
% 4.37/4.61          | (v2_struct_0 @ X15))),
% 4.37/4.61      inference('cnf', [status(esa)], [t26_tmap_1])).
% 4.37/4.61  thf('25', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | ~ (v2_pre_topc @ sk_A)
% 4.37/4.61        | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61        | ((k2_tsep_1 @ sk_A @ sk_D @ sk_D)
% 4.37/4.61            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('sup-', [status(thm)], ['23', '24'])).
% 4.37/4.61  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf(t25_tmap_1, axiom,
% 4.37/4.61    (![A:$i]:
% 4.37/4.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.37/4.61       ( ![B:$i]:
% 4.37/4.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.37/4.61           ( ( k1_tsep_1 @ A @ B @ B ) =
% 4.37/4.61             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 4.37/4.61  thf('29', plain,
% 4.37/4.61      (![X12 : $i, X13 : $i]:
% 4.37/4.61         ((v2_struct_0 @ X12)
% 4.37/4.61          | ~ (m1_pre_topc @ X12 @ X13)
% 4.37/4.61          | ((k1_tsep_1 @ X13 @ X12 @ X12)
% 4.37/4.61              = (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 4.37/4.61          | ~ (l1_pre_topc @ X13)
% 4.37/4.61          | ~ (v2_pre_topc @ X13)
% 4.37/4.61          | (v2_struct_0 @ X13))),
% 4.37/4.61      inference('cnf', [status(esa)], [t25_tmap_1])).
% 4.37/4.61  thf('30', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | ~ (v2_pre_topc @ sk_A)
% 4.37/4.61        | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 4.37/4.61            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('sup-', [status(thm)], ['28', '29'])).
% 4.37/4.61  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('33', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 4.37/4.61            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('demod', [status(thm)], ['30', '31', '32'])).
% 4.37/4.61  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('35', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 4.37/4.61            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 4.37/4.61      inference('clc', [status(thm)], ['33', '34'])).
% 4.37/4.61  thf('36', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('37', plain,
% 4.37/4.61      (((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 4.37/4.61         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 4.37/4.61      inference('clc', [status(thm)], ['35', '36'])).
% 4.37/4.61  thf('38', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | ((k2_tsep_1 @ sk_A @ sk_D @ sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('demod', [status(thm)], ['25', '26', '27', '37'])).
% 4.37/4.61  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('40', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | ((k2_tsep_1 @ sk_A @ sk_D @ sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 4.37/4.61      inference('clc', [status(thm)], ['38', '39'])).
% 4.37/4.61  thf('41', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('42', plain,
% 4.37/4.61      (((k2_tsep_1 @ sk_A @ sk_D @ sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['40', '41'])).
% 4.37/4.61  thf('43', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.37/4.61           (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A))),
% 4.37/4.61      inference('demod', [status(thm)], ['21', '22', '42'])).
% 4.37/4.61  thf('44', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 4.37/4.61           (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('simplify', [status(thm)], ['43'])).
% 4.37/4.61  thf('45', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['1', '6'])).
% 4.37/4.61  thf(t4_tsep_1, axiom,
% 4.37/4.61    (![A:$i]:
% 4.37/4.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.37/4.61       ( ![B:$i]:
% 4.37/4.61         ( ( m1_pre_topc @ B @ A ) =>
% 4.37/4.61           ( ![C:$i]:
% 4.37/4.61             ( ( m1_pre_topc @ C @ A ) =>
% 4.37/4.61               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 4.37/4.61                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 4.37/4.61  thf('46', plain,
% 4.37/4.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.37/4.61         (~ (m1_pre_topc @ X21 @ X22)
% 4.37/4.61          | ~ (m1_pre_topc @ X21 @ X23)
% 4.37/4.61          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))
% 4.37/4.61          | ~ (m1_pre_topc @ X23 @ X22)
% 4.37/4.61          | ~ (l1_pre_topc @ X22)
% 4.37/4.61          | ~ (v2_pre_topc @ X22))),
% 4.37/4.61      inference('cnf', [status(esa)], [t4_tsep_1])).
% 4.37/4.61  thf('47', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_B)
% 4.37/4.61          | ~ (v2_pre_topc @ sk_A)
% 4.37/4.61          | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 4.37/4.61             (u1_struct_0 @ X0))
% 4.37/4.61          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0))),
% 4.37/4.61      inference('sup-', [status(thm)], ['45', '46'])).
% 4.37/4.61  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('50', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_B)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 4.37/4.61             (u1_struct_0 @ X0))
% 4.37/4.61          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0))),
% 4.37/4.61      inference('demod', [status(thm)], ['47', '48', '49'])).
% 4.37/4.61  thf('51', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 4.37/4.61           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))
% 4.37/4.61        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C))),
% 4.37/4.61      inference('sup-', [status(thm)], ['44', '50'])).
% 4.37/4.61  thf('52', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('53', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('54', plain,
% 4.37/4.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.37/4.61         (~ (m1_pre_topc @ X9 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X9)
% 4.37/4.61          | ~ (l1_pre_topc @ X10)
% 4.37/4.61          | (v2_struct_0 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X11)
% 4.37/4.61          | ~ (m1_pre_topc @ X11 @ X10)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 4.37/4.61      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 4.37/4.61  thf('55', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('sup-', [status(thm)], ['53', '54'])).
% 4.37/4.61  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('57', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('demod', [status(thm)], ['55', '56'])).
% 4.37/4.61  thf('58', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['52', '57'])).
% 4.37/4.61  thf('59', plain,
% 4.37/4.61      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('simplify', [status(thm)], ['58'])).
% 4.37/4.61  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('61', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A))),
% 4.37/4.61      inference('clc', [status(thm)], ['59', '60'])).
% 4.37/4.61  thf('62', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('63', plain, ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)),
% 4.37/4.61      inference('clc', [status(thm)], ['61', '62'])).
% 4.37/4.61  thf('64', plain,
% 4.37/4.61      (((k2_tsep_1 @ sk_A @ sk_D @ sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['40', '41'])).
% 4.37/4.61  thf('65', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)),
% 4.37/4.61      inference('demod', [status(thm)], ['63', '64'])).
% 4.37/4.61  thf(d2_tsep_1, axiom,
% 4.37/4.61    (![A:$i]:
% 4.37/4.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 4.37/4.61       ( ![B:$i]:
% 4.37/4.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.37/4.61           ( ![C:$i]:
% 4.37/4.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 4.37/4.61               ( ![D:$i]:
% 4.37/4.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 4.37/4.61                     ( m1_pre_topc @ D @ A ) ) =>
% 4.37/4.61                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 4.37/4.61                     ( ( u1_struct_0 @ D ) =
% 4.37/4.61                       ( k2_xboole_0 @
% 4.37/4.61                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 4.37/4.61  thf('66', plain,
% 4.37/4.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.37/4.61         ((v2_struct_0 @ X5)
% 4.37/4.61          | ~ (m1_pre_topc @ X5 @ X6)
% 4.37/4.61          | (v2_struct_0 @ X7)
% 4.37/4.61          | ~ (v1_pre_topc @ X7)
% 4.37/4.61          | ~ (m1_pre_topc @ X7 @ X6)
% 4.37/4.61          | ((X7) != (k1_tsep_1 @ X6 @ X5 @ X8))
% 4.37/4.61          | ((u1_struct_0 @ X7)
% 4.37/4.61              = (k2_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X8)))
% 4.37/4.61          | ~ (m1_pre_topc @ X8 @ X6)
% 4.37/4.61          | (v2_struct_0 @ X8)
% 4.37/4.61          | ~ (l1_pre_topc @ X6)
% 4.37/4.61          | (v2_struct_0 @ X6))),
% 4.37/4.61      inference('cnf', [status(esa)], [d2_tsep_1])).
% 4.37/4.61  thf('67', plain,
% 4.37/4.61      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.37/4.61         ((v2_struct_0 @ X6)
% 4.37/4.61          | ~ (l1_pre_topc @ X6)
% 4.37/4.61          | (v2_struct_0 @ X8)
% 4.37/4.61          | ~ (m1_pre_topc @ X8 @ X6)
% 4.37/4.61          | ((u1_struct_0 @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 4.37/4.61              = (k2_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X8)))
% 4.37/4.61          | ~ (m1_pre_topc @ (k1_tsep_1 @ X6 @ X5 @ X8) @ X6)
% 4.37/4.61          | ~ (v1_pre_topc @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 4.37/4.61          | (v2_struct_0 @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 4.37/4.61          | ~ (m1_pre_topc @ X5 @ X6)
% 4.37/4.61          | (v2_struct_0 @ X5))),
% 4.37/4.61      inference('simplify', [status(thm)], ['66'])).
% 4.37/4.61  thf('68', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61            = (k2_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D)))
% 4.37/4.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['65', '67'])).
% 4.37/4.61  thf('69', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('71', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('72', plain,
% 4.37/4.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.37/4.61         (~ (m1_pre_topc @ X9 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X9)
% 4.37/4.61          | ~ (l1_pre_topc @ X10)
% 4.37/4.61          | (v2_struct_0 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X11)
% 4.37/4.61          | ~ (m1_pre_topc @ X11 @ X10)
% 4.37/4.61          | (v1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 4.37/4.61      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 4.37/4.61  thf('73', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('sup-', [status(thm)], ['71', '72'])).
% 4.37/4.61  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('75', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 4.37/4.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ X0)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('demod', [status(thm)], ['73', '74'])).
% 4.37/4.61  thf('76', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 4.37/4.61      inference('sup-', [status(thm)], ['70', '75'])).
% 4.37/4.61  thf('77', plain,
% 4.37/4.61      (((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('simplify', [status(thm)], ['76'])).
% 4.37/4.61  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('79', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D) | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 4.37/4.61      inference('clc', [status(thm)], ['77', '78'])).
% 4.37/4.61  thf('80', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('81', plain, ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['79', '80'])).
% 4.37/4.61  thf('82', plain,
% 4.37/4.61      (((k2_tsep_1 @ sk_A @ sk_D @ sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['40', '41'])).
% 4.37/4.61  thf('83', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('demod', [status(thm)], ['81', '82'])).
% 4.37/4.61  thf(d10_xboole_0, axiom,
% 4.37/4.61    (![A:$i,B:$i]:
% 4.37/4.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.37/4.61  thf('84', plain,
% 4.37/4.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.37/4.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.37/4.61  thf('85', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.37/4.61      inference('simplify', [status(thm)], ['84'])).
% 4.37/4.61  thf(t12_xboole_1, axiom,
% 4.37/4.61    (![A:$i,B:$i]:
% 4.37/4.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.37/4.61  thf('86', plain,
% 4.37/4.61      (![X3 : $i, X4 : $i]:
% 4.37/4.61         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 4.37/4.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.37/4.61  thf('87', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.37/4.61      inference('sup-', [status(thm)], ['85', '86'])).
% 4.37/4.61  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('90', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61            = (u1_struct_0 @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_A))),
% 4.37/4.61      inference('demod', [status(thm)], ['68', '69', '83', '87', '88', '89'])).
% 4.37/4.61  thf('91', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61            = (u1_struct_0 @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('simplify', [status(thm)], ['90'])).
% 4.37/4.61  thf('92', plain,
% 4.37/4.61      (((k2_tsep_1 @ sk_A @ sk_D @ sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['40', '41'])).
% 4.37/4.61  thf('93', plain,
% 4.37/4.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.37/4.61         (~ (m1_pre_topc @ X9 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X9)
% 4.37/4.61          | ~ (l1_pre_topc @ X10)
% 4.37/4.61          | (v2_struct_0 @ X10)
% 4.37/4.61          | (v2_struct_0 @ X11)
% 4.37/4.61          | ~ (m1_pre_topc @ X11 @ X10)
% 4.37/4.61          | ~ (v2_struct_0 @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 4.37/4.61      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 4.37/4.61  thf('94', plain,
% 4.37/4.61      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['92', '93'])).
% 4.37/4.61  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('98', plain,
% 4.37/4.61      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 4.37/4.61  thf('99', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | ~ (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 4.37/4.61      inference('simplify', [status(thm)], ['98'])).
% 4.37/4.61  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('101', plain,
% 4.37/4.61      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['99', '100'])).
% 4.37/4.61  thf('102', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('103', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['101', '102'])).
% 4.37/4.61  thf('104', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61            = (u1_struct_0 @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_A))),
% 4.37/4.61      inference('sup-', [status(thm)], ['91', '103'])).
% 4.37/4.61  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('106', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_A)
% 4.37/4.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 4.37/4.61            = (u1_struct_0 @ sk_D)))),
% 4.37/4.61      inference('clc', [status(thm)], ['104', '105'])).
% 4.37/4.61  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('108', plain,
% 4.37/4.61      (((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D)) = (u1_struct_0 @ sk_D))),
% 4.37/4.61      inference('clc', [status(thm)], ['106', '107'])).
% 4.37/4.61  thf('109', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D) @ sk_A)),
% 4.37/4.61      inference('demod', [status(thm)], ['63', '64'])).
% 4.37/4.61  thf('110', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 4.37/4.61           (u1_struct_0 @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C))),
% 4.37/4.61      inference('demod', [status(thm)], ['51', '108', '109'])).
% 4.37/4.61  thf('111', plain,
% 4.37/4.61      (((r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 4.37/4.61         (u1_struct_0 @ sk_D))
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('simplify', [status(thm)], ['110'])).
% 4.37/4.61  thf('112', plain,
% 4.37/4.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.37/4.61         (~ (m1_pre_topc @ X21 @ X22)
% 4.37/4.61          | ~ (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))
% 4.37/4.61          | (m1_pre_topc @ X21 @ X23)
% 4.37/4.61          | ~ (m1_pre_topc @ X23 @ X22)
% 4.37/4.61          | ~ (l1_pre_topc @ X22)
% 4.37/4.61          | ~ (v2_pre_topc @ X22))),
% 4.37/4.61      inference('cnf', [status(esa)], [t4_tsep_1])).
% 4.37/4.61  thf('113', plain,
% 4.37/4.61      (![X0 : $i]:
% 4.37/4.61         ((v2_struct_0 @ sk_B)
% 4.37/4.61          | (v2_struct_0 @ sk_D)
% 4.37/4.61          | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ sk_C)
% 4.37/4.61          | (v2_struct_0 @ sk_A)
% 4.37/4.61          | ~ (v2_pre_topc @ X0)
% 4.37/4.61          | ~ (l1_pre_topc @ X0)
% 4.37/4.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 4.37/4.61          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 4.37/4.61          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0))),
% 4.37/4.61      inference('sup-', [status(thm)], ['111', '112'])).
% 4.37/4.61  thf('114', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 4.37/4.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 4.37/4.61        | ~ (l1_pre_topc @ sk_A)
% 4.37/4.61        | ~ (v2_pre_topc @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('sup-', [status(thm)], ['7', '113'])).
% 4.37/4.61  thf('115', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('118', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 4.37/4.61  thf('119', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C))),
% 4.37/4.61      inference('simplify', [status(thm)], ['118'])).
% 4.37/4.61  thf('120', plain,
% 4.37/4.61      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('121', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (r1_tsep_1 @ sk_B @ sk_C)
% 4.37/4.61        | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('sup-', [status(thm)], ['119', '120'])).
% 4.37/4.61  thf('122', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('123', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_D)
% 4.37/4.61        | (v2_struct_0 @ sk_B)
% 4.37/4.61        | (v2_struct_0 @ sk_A)
% 4.37/4.61        | (v2_struct_0 @ sk_C))),
% 4.37/4.61      inference('sup-', [status(thm)], ['121', '122'])).
% 4.37/4.61  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('125', plain,
% 4.37/4.61      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 4.37/4.61      inference('sup-', [status(thm)], ['123', '124'])).
% 4.37/4.61  thf('126', plain, (~ (v2_struct_0 @ sk_C)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('127', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 4.37/4.61      inference('clc', [status(thm)], ['125', '126'])).
% 4.37/4.61  thf('128', plain, (~ (v2_struct_0 @ sk_D)),
% 4.37/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.61  thf('129', plain, ((v2_struct_0 @ sk_B)),
% 4.37/4.61      inference('clc', [status(thm)], ['127', '128'])).
% 4.37/4.61  thf('130', plain, ($false), inference('demod', [status(thm)], ['0', '129'])).
% 4.37/4.61  
% 4.37/4.61  % SZS output end Refutation
% 4.37/4.61  
% 4.37/4.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
