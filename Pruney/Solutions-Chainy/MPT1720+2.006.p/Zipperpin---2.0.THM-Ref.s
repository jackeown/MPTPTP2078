%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ePPbOcTG3O

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:28 EST 2020

% Result     : Theorem 3.37s
% Output     : Refutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  305 (1695 expanded)
%              Number of leaves         :   26 ( 468 expanded)
%              Depth                    :   34
%              Number of atoms          : 2976 (31857 expanded)
%              Number of equality atoms :   70 ( 207 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t29_tmap_1,conjecture,(
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
                 => ( ( ( m1_pre_topc @ B @ C )
                      & ( m1_pre_topc @ D @ C ) )
                   => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) )).

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
                   => ( ( ( m1_pre_topc @ B @ C )
                        & ( m1_pre_topc @ D @ C ) )
                     => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
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
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
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
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
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

thf('16',plain,(
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

thf('17',plain,(
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
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['42','43'])).

thf('46',plain,(
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
    inference(simplify,[status(thm)],['16'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','60','61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('67',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('79',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_tsep_1,axiom,(
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
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('82',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_pre_topc @ X19 @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('94',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k1_tsep_1 @ X23 @ X22 @ X22 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('103',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['92','110'])).

thf('112',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','111'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('113',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['76','114'])).

thf('116',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('117',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('119',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','119'])).

thf('121',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ X1 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','137'])).

thf('139',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_pre_topc @ X19 @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k1_tsep_1 @ X23 @ X22 @ X22 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','168'])).

thf('170',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['151','169'])).

thf('171',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ( k1_tsep_1 @ A @ B @ C )
        = ( k1_tsep_1 @ A @ C @ B ) ) ) )).

thf('172',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( ( k1_tsep_1 @ X10 @ X9 @ X11 )
        = ( k1_tsep_1 @ X10 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k1_tsep_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_C @ sk_D @ X0 )
        = ( k1_tsep_1 @ sk_C @ X0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_C @ sk_D @ X0 )
        = ( k1_tsep_1 @ sk_C @ X0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
      = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['170','175'])).

thf('177',plain,
    ( ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
      = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
      = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
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
    inference(simplify,[status(thm)],['16'])).

thf('183',plain,
    ( ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['151','169'])).

thf('185',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ X0 ) @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ X0 ) @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['184','189'])).

thf('191',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) @ sk_C ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['151','169'])).

thf('197',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('198',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('199',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['151','169'])).

thf('200',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','204'])).

thf('206',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('212',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['183','195','196','197','198','210','211','212','213'])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['193','194'])).

thf('217',plain,(
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
    inference(simplify,[status(thm)],['16'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('221',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['151','169'])).

thf('222',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219','220','221','222'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['225','231'])).

thf('233',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('236',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['224','236'])).

thf('238',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_D @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('239',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('240',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['166','167'])).

thf('243',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['151','169'])).

thf('244',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['240','241','242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['237','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( u1_struct_0 @ sk_C )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['215','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ sk_C )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( u1_struct_0 @ sk_C )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['259','260'])).

thf('262',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('263',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('264',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['261','264'])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['138','265'])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','266'])).

thf('268',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','168'])).

thf('270',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,(
    $false ),
    inference(demod,[status(thm)],['0','276'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ePPbOcTG3O
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 3.37/3.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.37/3.58  % Solved by: fo/fo7.sh
% 3.37/3.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.37/3.58  % done 2726 iterations in 3.131s
% 3.37/3.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.37/3.58  % SZS output start Refutation
% 3.37/3.58  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 3.37/3.58  thf(sk_A_type, type, sk_A: $i).
% 3.37/3.58  thf(sk_D_type, type, sk_D: $i).
% 3.37/3.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.37/3.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.37/3.58  thf(sk_C_type, type, sk_C: $i).
% 3.37/3.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.37/3.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.37/3.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.37/3.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.37/3.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.37/3.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 3.37/3.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.37/3.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.37/3.58  thf(sk_B_type, type, sk_B: $i).
% 3.37/3.58  thf(t29_tmap_1, conjecture,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.37/3.58       ( ![B:$i]:
% 3.37/3.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.37/3.58           ( ![C:$i]:
% 3.37/3.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.37/3.58               ( ![D:$i]:
% 3.37/3.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.37/3.58                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 3.37/3.58                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 3.37/3.58  thf(zf_stmt_0, negated_conjecture,
% 3.37/3.58    (~( ![A:$i]:
% 3.37/3.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.37/3.58            ( l1_pre_topc @ A ) ) =>
% 3.37/3.58          ( ![B:$i]:
% 3.37/3.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.37/3.58              ( ![C:$i]:
% 3.37/3.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.37/3.58                  ( ![D:$i]:
% 3.37/3.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.37/3.58                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 3.37/3.58                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 3.37/3.58    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 3.37/3.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(dt_k1_tsep_1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i]:
% 3.37/3.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 3.37/3.58         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 3.37/3.58         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.37/3.58       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 3.37/3.58         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 3.37/3.58         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 3.37/3.58  thf('3', plain,
% 3.37/3.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X16)
% 3.37/3.58          | ~ (l1_pre_topc @ X17)
% 3.37/3.58          | (v2_struct_0 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X18)
% 3.37/3.58          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.58          | (m1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18) @ X17))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.58  thf('4', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['2', '3'])).
% 3.37/3.58  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('6', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['4', '5'])).
% 3.37/3.58  thf('7', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['1', '6'])).
% 3.37/3.58  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('10', plain,
% 3.37/3.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X16)
% 3.37/3.58          | ~ (l1_pre_topc @ X17)
% 3.37/3.58          | (v2_struct_0 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X18)
% 3.37/3.58          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.58          | (v1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.58  thf('11', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['9', '10'])).
% 3.37/3.58  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('13', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['11', '12'])).
% 3.37/3.58  thf('14', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['8', '13'])).
% 3.37/3.58  thf('15', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['1', '6'])).
% 3.37/3.58  thf(d2_tsep_1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 3.37/3.58       ( ![B:$i]:
% 3.37/3.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.37/3.58           ( ![C:$i]:
% 3.37/3.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.37/3.58               ( ![D:$i]:
% 3.37/3.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 3.37/3.58                     ( m1_pre_topc @ D @ A ) ) =>
% 3.37/3.58                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 3.37/3.58                     ( ( u1_struct_0 @ D ) =
% 3.37/3.58                       ( k2_xboole_0 @
% 3.37/3.58                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 3.37/3.58  thf('16', plain,
% 3.37/3.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.37/3.58         ((v2_struct_0 @ X12)
% 3.37/3.58          | ~ (m1_pre_topc @ X12 @ X13)
% 3.37/3.58          | (v2_struct_0 @ X14)
% 3.37/3.58          | ~ (v1_pre_topc @ X14)
% 3.37/3.58          | ~ (m1_pre_topc @ X14 @ X13)
% 3.37/3.58          | ((X14) != (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58          | ((u1_struct_0 @ X14)
% 3.37/3.58              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 3.37/3.58          | ~ (m1_pre_topc @ X15 @ X13)
% 3.37/3.58          | (v2_struct_0 @ X15)
% 3.37/3.58          | ~ (l1_pre_topc @ X13)
% 3.37/3.58          | (v2_struct_0 @ X13))),
% 3.37/3.58      inference('cnf', [status(esa)], [d2_tsep_1])).
% 3.37/3.58  thf('17', plain,
% 3.37/3.58      (![X12 : $i, X13 : $i, X15 : $i]:
% 3.37/3.58         ((v2_struct_0 @ X13)
% 3.37/3.58          | ~ (l1_pre_topc @ X13)
% 3.37/3.58          | (v2_struct_0 @ X15)
% 3.37/3.58          | ~ (m1_pre_topc @ X15 @ X13)
% 3.37/3.58          | ((u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 3.37/3.58          | ~ (m1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X13)
% 3.37/3.58          | ~ (v1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58          | (v2_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58          | ~ (m1_pre_topc @ X12 @ X13)
% 3.37/3.58          | (v2_struct_0 @ X12))),
% 3.37/3.58      inference('simplify', [status(thm)], ['16'])).
% 3.37/3.58  thf('18', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['15', '17'])).
% 3.37/3.58  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('22', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A))),
% 3.37/3.58      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 3.37/3.58  thf('23', plain,
% 3.37/3.58      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D))),
% 3.37/3.58      inference('simplify', [status(thm)], ['22'])).
% 3.37/3.58  thf('24', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['14', '23'])).
% 3.37/3.58  thf('25', plain,
% 3.37/3.58      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D))),
% 3.37/3.58      inference('simplify', [status(thm)], ['24'])).
% 3.37/3.58  thf('26', plain,
% 3.37/3.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X16)
% 3.37/3.58          | ~ (l1_pre_topc @ X17)
% 3.37/3.58          | (v2_struct_0 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X18)
% 3.37/3.58          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.58          | ~ (v2_struct_0 @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.58  thf('27', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['25', '26'])).
% 3.37/3.58  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('31', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | (v2_struct_0 @ sk_D)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 3.37/3.58  thf('32', plain,
% 3.37/3.58      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 3.37/3.58          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_D))),
% 3.37/3.58      inference('simplify', [status(thm)], ['31'])).
% 3.37/3.58  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('35', plain,
% 3.37/3.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X16)
% 3.37/3.58          | ~ (l1_pre_topc @ X17)
% 3.37/3.58          | (v2_struct_0 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X18)
% 3.37/3.58          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.58          | (m1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18) @ X17))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.58  thf('36', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('sup-', [status(thm)], ['34', '35'])).
% 3.37/3.58  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('38', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('demod', [status(thm)], ['36', '37'])).
% 3.37/3.58  thf('39', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_C)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_C)
% 3.37/3.58        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['33', '38'])).
% 3.37/3.58  thf('40', plain,
% 3.37/3.58      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('simplify', [status(thm)], ['39'])).
% 3.37/3.58  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('42', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_C)
% 3.37/3.58        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A))),
% 3.37/3.58      inference('clc', [status(thm)], ['40', '41'])).
% 3.37/3.58  thf('43', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('44', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)),
% 3.37/3.58      inference('clc', [status(thm)], ['42', '43'])).
% 3.37/3.58  thf('45', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)),
% 3.37/3.58      inference('clc', [status(thm)], ['42', '43'])).
% 3.37/3.58  thf('46', plain,
% 3.37/3.58      (![X12 : $i, X13 : $i, X15 : $i]:
% 3.37/3.58         ((v2_struct_0 @ X13)
% 3.37/3.58          | ~ (l1_pre_topc @ X13)
% 3.37/3.58          | (v2_struct_0 @ X15)
% 3.37/3.58          | ~ (m1_pre_topc @ X15 @ X13)
% 3.37/3.58          | ((u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 3.37/3.58          | ~ (m1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X13)
% 3.37/3.58          | ~ (v1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58          | (v2_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.58          | ~ (m1_pre_topc @ X12 @ X13)
% 3.37/3.58          | (v2_struct_0 @ X12))),
% 3.37/3.58      inference('simplify', [status(thm)], ['16'])).
% 3.37/3.58  thf('47', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_C)
% 3.37/3.58        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 3.37/3.58        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_C)
% 3.37/3.58        | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['45', '46'])).
% 3.37/3.58  thf('48', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('50', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('51', plain,
% 3.37/3.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X16)
% 3.37/3.58          | ~ (l1_pre_topc @ X17)
% 3.37/3.58          | (v2_struct_0 @ X17)
% 3.37/3.58          | (v2_struct_0 @ X18)
% 3.37/3.58          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.58          | (v1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.58  thf('52', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('sup-', [status(thm)], ['50', '51'])).
% 3.37/3.58  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('54', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | (v2_struct_0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('demod', [status(thm)], ['52', '53'])).
% 3.37/3.58  thf('55', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_C)
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_C)
% 3.37/3.58        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['49', '54'])).
% 3.37/3.58  thf('56', plain,
% 3.37/3.58      (((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58        | (v2_struct_0 @ sk_A)
% 3.37/3.58        | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('simplify', [status(thm)], ['55'])).
% 3.37/3.58  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('58', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_C) | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 3.37/3.58      inference('clc', [status(thm)], ['56', '57'])).
% 3.37/3.58  thf('59', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('60', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 3.37/3.58      inference('clc', [status(thm)], ['58', '59'])).
% 3.37/3.58  thf('61', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('63', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_C)
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 3.37/3.58        | (v2_struct_0 @ sk_C)
% 3.37/3.58        | (v2_struct_0 @ sk_A))),
% 3.37/3.58      inference('demod', [status(thm)], ['47', '48', '60', '61', '62'])).
% 3.37/3.58  thf('64', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_A)
% 3.37/3.58        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 3.37/3.58        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.58        | (v2_struct_0 @ sk_C))),
% 3.37/3.58      inference('simplify', [status(thm)], ['63'])).
% 3.37/3.58  thf('65', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(t4_tsep_1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.37/3.58       ( ![B:$i]:
% 3.37/3.58         ( ( m1_pre_topc @ B @ A ) =>
% 3.37/3.58           ( ![C:$i]:
% 3.37/3.58             ( ( m1_pre_topc @ C @ A ) =>
% 3.37/3.58               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 3.37/3.58                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 3.37/3.58  thf('67', plain,
% 3.37/3.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X24 @ X25)
% 3.37/3.58          | ~ (m1_pre_topc @ X24 @ X26)
% 3.37/3.58          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 3.37/3.58          | ~ (m1_pre_topc @ X26 @ X25)
% 3.37/3.58          | ~ (l1_pre_topc @ X25)
% 3.37/3.58          | ~ (v2_pre_topc @ X25))),
% 3.37/3.58      inference('cnf', [status(esa)], [t4_tsep_1])).
% 3.37/3.58  thf('68', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (v2_pre_topc @ sk_A)
% 3.37/3.58          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ sk_B @ X0))),
% 3.37/3.58      inference('sup-', [status(thm)], ['66', '67'])).
% 3.37/3.58  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('71', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ sk_B @ X0))),
% 3.37/3.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 3.37/3.58  thf('72', plain,
% 3.37/3.58      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 3.37/3.58        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['65', '71'])).
% 3.37/3.58  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('74', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 3.37/3.58      inference('demod', [status(thm)], ['72', '73'])).
% 3.37/3.58  thf(t12_xboole_1, axiom,
% 3.37/3.58    (![A:$i,B:$i]:
% 3.37/3.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.37/3.58  thf('75', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i]:
% 3.37/3.58         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 3.37/3.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.37/3.58  thf('76', plain,
% 3.37/3.58      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 3.37/3.58         = (u1_struct_0 @ sk_C))),
% 3.37/3.58      inference('sup-', [status(thm)], ['74', '75'])).
% 3.37/3.58  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('78', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 3.37/3.58          | ~ (m1_pre_topc @ sk_B @ X0))),
% 3.37/3.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 3.37/3.58  thf('79', plain,
% 3.37/3.58      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 3.37/3.58        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['77', '78'])).
% 3.37/3.58  thf('80', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(t22_tsep_1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.37/3.58       ( ![B:$i]:
% 3.37/3.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.37/3.58           ( ![C:$i]:
% 3.37/3.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.37/3.58               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 3.37/3.58  thf('82', plain,
% 3.37/3.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.37/3.58         ((v2_struct_0 @ X19)
% 3.37/3.58          | ~ (m1_pre_topc @ X19 @ X20)
% 3.37/3.58          | (m1_pre_topc @ X19 @ (k1_tsep_1 @ X20 @ X19 @ X21))
% 3.37/3.58          | ~ (m1_pre_topc @ X21 @ X20)
% 3.37/3.58          | (v2_struct_0 @ X21)
% 3.37/3.58          | ~ (l1_pre_topc @ X20)
% 3.37/3.58          | ~ (v2_pre_topc @ X20)
% 3.37/3.58          | (v2_struct_0 @ X20))),
% 3.37/3.58      inference('cnf', [status(esa)], [t22_tsep_1])).
% 3.37/3.58  thf('83', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((v2_struct_0 @ sk_A)
% 3.37/3.58          | ~ (v2_pre_topc @ sk_A)
% 3.37/3.58          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 3.37/3.58          | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['81', '82'])).
% 3.37/3.58  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('86', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((v2_struct_0 @ sk_A)
% 3.37/3.58          | (v2_struct_0 @ X0)
% 3.37/3.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.58          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 3.37/3.58          | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['83', '84', '85'])).
% 3.37/3.58  thf('87', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_B)
% 3.37/3.58        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 3.37/3.58        | (v2_struct_0 @ sk_B)
% 3.37/3.58        | (v2_struct_0 @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['80', '86'])).
% 3.37/3.58  thf('88', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_A)
% 3.37/3.58        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 3.37/3.58        | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('simplify', [status(thm)], ['87'])).
% 3.37/3.58  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('90', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_B)
% 3.37/3.58        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B)))),
% 3.37/3.58      inference('clc', [status(thm)], ['88', '89'])).
% 3.37/3.58  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('92', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))),
% 3.37/3.58      inference('clc', [status(thm)], ['90', '91'])).
% 3.37/3.58  thf('93', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(t25_tmap_1, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.37/3.58       ( ![B:$i]:
% 3.37/3.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.37/3.58           ( ( k1_tsep_1 @ A @ B @ B ) =
% 3.37/3.58             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 3.37/3.58  thf('94', plain,
% 3.37/3.58      (![X22 : $i, X23 : $i]:
% 3.37/3.58         ((v2_struct_0 @ X22)
% 3.37/3.58          | ~ (m1_pre_topc @ X22 @ X23)
% 3.37/3.58          | ((k1_tsep_1 @ X23 @ X22 @ X22)
% 3.37/3.58              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 3.37/3.58          | ~ (l1_pre_topc @ X23)
% 3.37/3.58          | ~ (v2_pre_topc @ X23)
% 3.37/3.58          | (v2_struct_0 @ X23))),
% 3.37/3.58      inference('cnf', [status(esa)], [t25_tmap_1])).
% 3.37/3.58  thf('95', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_A)
% 3.37/3.58        | ~ (v2_pre_topc @ sk_A)
% 3.37/3.58        | ~ (l1_pre_topc @ sk_A)
% 3.37/3.58        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 3.37/3.58            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 3.37/3.58        | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['93', '94'])).
% 3.37/3.58  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('98', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_A)
% 3.37/3.58        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 3.37/3.58            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 3.37/3.58        | (v2_struct_0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['95', '96', '97'])).
% 3.37/3.58  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('100', plain,
% 3.37/3.58      (((v2_struct_0 @ sk_B)
% 3.37/3.58        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 3.37/3.58            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 3.37/3.58      inference('clc', [status(thm)], ['98', '99'])).
% 3.37/3.58  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('102', plain,
% 3.37/3.58      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 3.37/3.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 3.37/3.58      inference('clc', [status(thm)], ['100', '101'])).
% 3.37/3.58  thf(t59_pre_topc, axiom,
% 3.37/3.58    (![A:$i]:
% 3.37/3.58     ( ( l1_pre_topc @ A ) =>
% 3.37/3.58       ( ![B:$i]:
% 3.37/3.58         ( ( m1_pre_topc @
% 3.37/3.58             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 3.37/3.58           ( m1_pre_topc @ B @ A ) ) ) ))).
% 3.37/3.58  thf('103', plain,
% 3.37/3.58      (![X7 : $i, X8 : $i]:
% 3.37/3.58         (~ (m1_pre_topc @ X7 @ 
% 3.37/3.58             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 3.37/3.59          | (m1_pre_topc @ X7 @ X8)
% 3.37/3.59          | ~ (l1_pre_topc @ X8))),
% 3.37/3.59      inference('cnf', [status(esa)], [t59_pre_topc])).
% 3.37/3.59  thf('104', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 3.37/3.59          | ~ (l1_pre_topc @ sk_B)
% 3.37/3.59          | (m1_pre_topc @ X0 @ sk_B))),
% 3.37/3.59      inference('sup-', [status(thm)], ['102', '103'])).
% 3.37/3.59  thf('105', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf(dt_m1_pre_topc, axiom,
% 3.37/3.59    (![A:$i]:
% 3.37/3.59     ( ( l1_pre_topc @ A ) =>
% 3.37/3.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.37/3.59  thf('106', plain,
% 3.37/3.59      (![X5 : $i, X6 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.37/3.59  thf('107', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 3.37/3.59      inference('sup-', [status(thm)], ['105', '106'])).
% 3.37/3.59  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 3.37/3.59      inference('demod', [status(thm)], ['107', '108'])).
% 3.37/3.59  thf('110', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 3.37/3.59          | (m1_pre_topc @ X0 @ sk_B))),
% 3.37/3.59      inference('demod', [status(thm)], ['104', '109'])).
% 3.37/3.59  thf('111', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 3.37/3.59      inference('sup-', [status(thm)], ['92', '110'])).
% 3.37/3.59  thf('112', plain,
% 3.37/3.59      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 3.37/3.59      inference('demod', [status(thm)], ['79', '111'])).
% 3.37/3.59  thf(t9_xboole_1, axiom,
% 3.37/3.59    (![A:$i,B:$i,C:$i]:
% 3.37/3.59     ( ( r1_tarski @ A @ B ) =>
% 3.37/3.59       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.37/3.59  thf('113', plain,
% 3.37/3.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.37/3.59         (~ (r1_tarski @ X2 @ X3)
% 3.37/3.59          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ (k2_xboole_0 @ X3 @ X4)))),
% 3.37/3.59      inference('cnf', [status(esa)], [t9_xboole_1])).
% 3.37/3.59  thf('114', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (r1_tarski @ (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0) @ 
% 3.37/3.59          (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 3.37/3.59      inference('sup-', [status(thm)], ['112', '113'])).
% 3.37/3.59  thf('115', plain,
% 3.37/3.59      ((r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 3.37/3.59        (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 3.37/3.59      inference('sup+', [status(thm)], ['76', '114'])).
% 3.37/3.59  thf('116', plain,
% 3.37/3.59      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 3.37/3.59         = (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['74', '75'])).
% 3.37/3.59  thf('117', plain,
% 3.37/3.59      ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['115', '116'])).
% 3.37/3.59  thf('118', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]:
% 3.37/3.59         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 3.37/3.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.37/3.59  thf('119', plain,
% 3.37/3.59      (((k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 3.37/3.59         = (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['117', '118'])).
% 3.37/3.59  thf('120', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_A)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['64', '119'])).
% 3.37/3.59  thf('121', plain,
% 3.37/3.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X16)
% 3.37/3.59          | ~ (l1_pre_topc @ X17)
% 3.37/3.59          | (v2_struct_0 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X18)
% 3.37/3.59          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.59          | ~ (v2_struct_0 @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.59  thf('122', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | ~ (l1_pre_topc @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 3.37/3.59      inference('sup-', [status(thm)], ['120', '121'])).
% 3.37/3.59  thf('123', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('125', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('126', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 3.37/3.59  thf('127', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_A)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('simplify', [status(thm)], ['126'])).
% 3.37/3.59  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('129', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C)))),
% 3.37/3.59      inference('clc', [status(thm)], ['127', '128'])).
% 3.37/3.59  thf('130', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('131', plain,
% 3.37/3.59      (((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)) = (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['129', '130'])).
% 3.37/3.59  thf('132', plain,
% 3.37/3.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X24 @ X25)
% 3.37/3.59          | ~ (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 3.37/3.59          | (m1_pre_topc @ X24 @ X26)
% 3.37/3.59          | ~ (m1_pre_topc @ X26 @ X25)
% 3.37/3.59          | ~ (l1_pre_topc @ X25)
% 3.37/3.59          | ~ (v2_pre_topc @ X25))),
% 3.37/3.59      inference('cnf', [status(esa)], [t4_tsep_1])).
% 3.37/3.59  thf('133', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]:
% 3.37/3.59         (~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C))
% 3.37/3.59          | ~ (v2_pre_topc @ X1)
% 3.37/3.59          | ~ (l1_pre_topc @ X1)
% 3.37/3.59          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ X1)
% 3.37/3.59          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.37/3.59      inference('sup-', [status(thm)], ['131', '132'])).
% 3.37/3.59  thf('134', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.59          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.59          | ~ (v2_pre_topc @ sk_A)
% 3.37/3.59          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C)))),
% 3.37/3.59      inference('sup-', [status(thm)], ['44', '133'])).
% 3.37/3.59  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('137', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.59          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C)))),
% 3.37/3.59      inference('demod', [status(thm)], ['134', '135', '136'])).
% 3.37/3.59  thf('138', plain,
% 3.37/3.59      ((~ (r1_tarski @ 
% 3.37/3.59           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 3.37/3.59           (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_B)
% 3.37/3.59        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 3.37/3.59           (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 3.37/3.59      inference('sup-', [status(thm)], ['32', '137'])).
% 3.37/3.59  thf('139', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('140', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('141', plain,
% 3.37/3.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.37/3.59         ((v2_struct_0 @ X19)
% 3.37/3.59          | ~ (m1_pre_topc @ X19 @ X20)
% 3.37/3.59          | (m1_pre_topc @ X19 @ (k1_tsep_1 @ X20 @ X19 @ X21))
% 3.37/3.59          | ~ (m1_pre_topc @ X21 @ X20)
% 3.37/3.59          | (v2_struct_0 @ X21)
% 3.37/3.59          | ~ (l1_pre_topc @ X20)
% 3.37/3.59          | ~ (v2_pre_topc @ X20)
% 3.37/3.59          | (v2_struct_0 @ X20))),
% 3.37/3.59      inference('cnf', [status(esa)], [t22_tsep_1])).
% 3.37/3.59  thf('142', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((v2_struct_0 @ sk_A)
% 3.37/3.59          | ~ (v2_pre_topc @ sk_A)
% 3.37/3.59          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.59          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 3.37/3.59          | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['140', '141'])).
% 3.37/3.59  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('145', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((v2_struct_0 @ sk_A)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.59          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 3.37/3.59          | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['142', '143', '144'])).
% 3.37/3.59  thf('146', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_A))),
% 3.37/3.59      inference('sup-', [status(thm)], ['139', '145'])).
% 3.37/3.59  thf('147', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_A)
% 3.37/3.59        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('simplify', [status(thm)], ['146'])).
% 3.37/3.59  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('149', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 3.37/3.59      inference('clc', [status(thm)], ['147', '148'])).
% 3.37/3.59  thf('150', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('151', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['149', '150'])).
% 3.37/3.59  thf('152', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('153', plain,
% 3.37/3.59      (![X22 : $i, X23 : $i]:
% 3.37/3.59         ((v2_struct_0 @ X22)
% 3.37/3.59          | ~ (m1_pre_topc @ X22 @ X23)
% 3.37/3.59          | ((k1_tsep_1 @ X23 @ X22 @ X22)
% 3.37/3.59              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 3.37/3.59          | ~ (l1_pre_topc @ X23)
% 3.37/3.59          | ~ (v2_pre_topc @ X23)
% 3.37/3.59          | (v2_struct_0 @ X23))),
% 3.37/3.59      inference('cnf', [status(esa)], [t25_tmap_1])).
% 3.37/3.59  thf('154', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_A)
% 3.37/3.59        | ~ (v2_pre_topc @ sk_A)
% 3.37/3.59        | ~ (l1_pre_topc @ sk_A)
% 3.37/3.59        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 3.37/3.59            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['152', '153'])).
% 3.37/3.59  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('157', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_A)
% 3.37/3.59        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 3.37/3.59            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['154', '155', '156'])).
% 3.37/3.59  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('159', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 3.37/3.59            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 3.37/3.59      inference('clc', [status(thm)], ['157', '158'])).
% 3.37/3.59  thf('160', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('161', plain,
% 3.37/3.59      (((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 3.37/3.59         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 3.37/3.59      inference('clc', [status(thm)], ['159', '160'])).
% 3.37/3.59  thf('162', plain,
% 3.37/3.59      (![X7 : $i, X8 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X7 @ 
% 3.37/3.59             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 3.37/3.59          | (m1_pre_topc @ X7 @ X8)
% 3.37/3.59          | ~ (l1_pre_topc @ X8))),
% 3.37/3.59      inference('cnf', [status(esa)], [t59_pre_topc])).
% 3.37/3.59  thf('163', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59          | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59          | (m1_pre_topc @ X0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['161', '162'])).
% 3.37/3.59  thf('164', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('165', plain,
% 3.37/3.59      (![X5 : $i, X6 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.37/3.59  thf('166', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['164', '165'])).
% 3.37/3.59  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('168', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('169', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59          | (m1_pre_topc @ X0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['163', '168'])).
% 3.37/3.59  thf('170', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.37/3.59      inference('sup-', [status(thm)], ['151', '169'])).
% 3.37/3.59  thf('171', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf(commutativity_k1_tsep_1, axiom,
% 3.37/3.59    (![A:$i,B:$i,C:$i]:
% 3.37/3.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 3.37/3.59         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 3.37/3.59         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.37/3.59       ( ( k1_tsep_1 @ A @ B @ C ) = ( k1_tsep_1 @ A @ C @ B ) ) ))).
% 3.37/3.59  thf('172', plain,
% 3.37/3.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X9 @ X10)
% 3.37/3.59          | (v2_struct_0 @ X9)
% 3.37/3.59          | ~ (l1_pre_topc @ X10)
% 3.37/3.59          | (v2_struct_0 @ X10)
% 3.37/3.59          | (v2_struct_0 @ X11)
% 3.37/3.59          | ~ (m1_pre_topc @ X11 @ X10)
% 3.37/3.59          | ((k1_tsep_1 @ X10 @ X9 @ X11) = (k1_tsep_1 @ X10 @ X11 @ X9)))),
% 3.37/3.59      inference('cnf', [status(esa)], [commutativity_k1_tsep_1])).
% 3.37/3.59  thf('173', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (((k1_tsep_1 @ sk_C @ sk_D @ X0) = (k1_tsep_1 @ sk_C @ X0 @ sk_D))
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | (v2_struct_0 @ sk_C)
% 3.37/3.59          | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('sup-', [status(thm)], ['171', '172'])).
% 3.37/3.59  thf('174', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('175', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (((k1_tsep_1 @ sk_C @ sk_D @ X0) = (k1_tsep_1 @ sk_C @ X0 @ sk_D))
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | (v2_struct_0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('demod', [status(thm)], ['173', '174'])).
% 3.37/3.59  thf('176', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | ((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D)))),
% 3.37/3.59      inference('sup-', [status(thm)], ['170', '175'])).
% 3.37/3.59  thf('177', plain,
% 3.37/3.59      ((((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D))
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('simplify', [status(thm)], ['176'])).
% 3.37/3.59  thf('178', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('179', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | ((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D)))),
% 3.37/3.59      inference('clc', [status(thm)], ['177', '178'])).
% 3.37/3.59  thf('180', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('181', plain,
% 3.37/3.59      (((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D))),
% 3.37/3.59      inference('clc', [status(thm)], ['179', '180'])).
% 3.37/3.59  thf('182', plain,
% 3.37/3.59      (![X12 : $i, X13 : $i, X15 : $i]:
% 3.37/3.59         ((v2_struct_0 @ X13)
% 3.37/3.59          | ~ (l1_pre_topc @ X13)
% 3.37/3.59          | (v2_struct_0 @ X15)
% 3.37/3.59          | ~ (m1_pre_topc @ X15 @ X13)
% 3.37/3.59          | ((u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.59              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 3.37/3.59          | ~ (m1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X13)
% 3.37/3.59          | ~ (v1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.59          | (v2_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.59          | ~ (m1_pre_topc @ X12 @ X13)
% 3.37/3.59          | (v2_struct_0 @ X12))),
% 3.37/3.59      inference('simplify', [status(thm)], ['16'])).
% 3.37/3.59  thf('183', plain,
% 3.37/3.59      ((~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C) @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_D))
% 3.37/3.59        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_D))
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_D))
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 3.37/3.59        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_D)
% 3.37/3.59        | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['181', '182'])).
% 3.37/3.59  thf('184', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.37/3.59      inference('sup-', [status(thm)], ['151', '169'])).
% 3.37/3.59  thf('185', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('186', plain,
% 3.37/3.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X16)
% 3.37/3.59          | ~ (l1_pre_topc @ X17)
% 3.37/3.59          | (v2_struct_0 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X18)
% 3.37/3.59          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.59          | (m1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18) @ X17))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.59  thf('187', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ X0) @ sk_C)
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | (v2_struct_0 @ sk_C)
% 3.37/3.59          | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('sup-', [status(thm)], ['185', '186'])).
% 3.37/3.59  thf('188', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('189', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ X0) @ sk_C)
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | (v2_struct_0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('demod', [status(thm)], ['187', '188'])).
% 3.37/3.59  thf('190', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C) @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['184', '189'])).
% 3.37/3.59  thf('191', plain,
% 3.37/3.59      (((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C) @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('simplify', [status(thm)], ['190'])).
% 3.37/3.59  thf('192', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('193', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C) @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['191', '192'])).
% 3.37/3.59  thf('194', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('195', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C) @ sk_C)),
% 3.37/3.59      inference('clc', [status(thm)], ['193', '194'])).
% 3.37/3.59  thf('196', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.37/3.59      inference('sup-', [status(thm)], ['151', '169'])).
% 3.37/3.59  thf('197', plain,
% 3.37/3.59      (((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D))),
% 3.37/3.59      inference('clc', [status(thm)], ['179', '180'])).
% 3.37/3.59  thf('198', plain,
% 3.37/3.59      (((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D))),
% 3.37/3.59      inference('clc', [status(thm)], ['179', '180'])).
% 3.37/3.59  thf('199', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.37/3.59      inference('sup-', [status(thm)], ['151', '169'])).
% 3.37/3.59  thf('200', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('201', plain,
% 3.37/3.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X16)
% 3.37/3.59          | ~ (l1_pre_topc @ X17)
% 3.37/3.59          | (v2_struct_0 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X18)
% 3.37/3.59          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.59          | (v1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.59  thf('202', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ X0))
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | (v2_struct_0 @ sk_C)
% 3.37/3.59          | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('sup-', [status(thm)], ['200', '201'])).
% 3.37/3.59  thf('203', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('204', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ X0))
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ X0)
% 3.37/3.59          | (v2_struct_0 @ sk_C)
% 3.37/3.59          | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('demod', [status(thm)], ['202', '203'])).
% 3.37/3.59  thf('205', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C)))),
% 3.37/3.59      inference('sup-', [status(thm)], ['199', '204'])).
% 3.37/3.59  thf('206', plain,
% 3.37/3.59      (((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('simplify', [status(thm)], ['205'])).
% 3.37/3.59  thf('207', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('208', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D) | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C)))),
% 3.37/3.59      inference('clc', [status(thm)], ['206', '207'])).
% 3.37/3.59  thf('209', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('210', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['208', '209'])).
% 3.37/3.59  thf('211', plain,
% 3.37/3.59      (((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D))),
% 3.37/3.59      inference('clc', [status(thm)], ['179', '180'])).
% 3.37/3.59  thf('212', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('213', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('214', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 3.37/3.59        | (v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)],
% 3.37/3.59                ['183', '195', '196', '197', '198', '210', '211', '212', '213'])).
% 3.37/3.59  thf('215', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('simplify', [status(thm)], ['214'])).
% 3.37/3.59  thf('216', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C) @ sk_C)),
% 3.37/3.59      inference('clc', [status(thm)], ['193', '194'])).
% 3.37/3.59  thf('217', plain,
% 3.37/3.59      (![X12 : $i, X13 : $i, X15 : $i]:
% 3.37/3.59         ((v2_struct_0 @ X13)
% 3.37/3.59          | ~ (l1_pre_topc @ X13)
% 3.37/3.59          | (v2_struct_0 @ X15)
% 3.37/3.59          | ~ (m1_pre_topc @ X15 @ X13)
% 3.37/3.59          | ((u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.59              = (k2_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X15)))
% 3.37/3.59          | ~ (m1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X13)
% 3.37/3.59          | ~ (v1_pre_topc @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.59          | (v2_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15))
% 3.37/3.59          | ~ (m1_pre_topc @ X12 @ X13)
% 3.37/3.59          | (v2_struct_0 @ X12))),
% 3.37/3.59      inference('simplify', [status(thm)], ['16'])).
% 3.37/3.59  thf('218', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 3.37/3.59        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['216', '217'])).
% 3.37/3.59  thf('219', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('220', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['208', '209'])).
% 3.37/3.59  thf('221', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.37/3.59      inference('sup-', [status(thm)], ['151', '169'])).
% 3.37/3.59  thf('222', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('223', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['218', '219', '220', '221', '222'])).
% 3.37/3.59  thf('224', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('simplify', [status(thm)], ['223'])).
% 3.37/3.59  thf('225', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('226', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('227', plain,
% 3.37/3.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X24 @ X25)
% 3.37/3.59          | ~ (m1_pre_topc @ X24 @ X26)
% 3.37/3.59          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 3.37/3.59          | ~ (m1_pre_topc @ X26 @ X25)
% 3.37/3.59          | ~ (l1_pre_topc @ X25)
% 3.37/3.59          | ~ (v2_pre_topc @ X25))),
% 3.37/3.59      inference('cnf', [status(esa)], [t4_tsep_1])).
% 3.37/3.59  thf('228', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (v2_pre_topc @ sk_A)
% 3.37/3.59          | ~ (l1_pre_topc @ sk_A)
% 3.37/3.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.59          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 3.37/3.59          | ~ (m1_pre_topc @ sk_D @ X0))),
% 3.37/3.59      inference('sup-', [status(thm)], ['226', '227'])).
% 3.37/3.59  thf('229', plain, ((v2_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('230', plain, ((l1_pre_topc @ sk_A)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('231', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.37/3.59          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 3.37/3.59          | ~ (m1_pre_topc @ sk_D @ X0))),
% 3.37/3.59      inference('demod', [status(thm)], ['228', '229', '230'])).
% 3.37/3.59  thf('232', plain,
% 3.37/3.59      ((~ (m1_pre_topc @ sk_D @ sk_C)
% 3.37/3.59        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 3.37/3.59      inference('sup-', [status(thm)], ['225', '231'])).
% 3.37/3.59  thf('233', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('234', plain,
% 3.37/3.59      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['232', '233'])).
% 3.37/3.59  thf('235', plain,
% 3.37/3.59      (![X0 : $i, X1 : $i]:
% 3.37/3.59         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 3.37/3.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.37/3.59  thf('236', plain,
% 3.37/3.59      (((k2_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 3.37/3.59         = (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['234', '235'])).
% 3.37/3.59  thf('237', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('demod', [status(thm)], ['224', '236'])).
% 3.37/3.59  thf('238', plain,
% 3.37/3.59      (((k1_tsep_1 @ sk_C @ sk_D @ sk_C) = (k1_tsep_1 @ sk_C @ sk_C @ sk_D))),
% 3.37/3.59      inference('clc', [status(thm)], ['179', '180'])).
% 3.37/3.59  thf('239', plain,
% 3.37/3.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X16 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X16)
% 3.37/3.59          | ~ (l1_pre_topc @ X17)
% 3.37/3.59          | (v2_struct_0 @ X17)
% 3.37/3.59          | (v2_struct_0 @ X18)
% 3.37/3.59          | ~ (m1_pre_topc @ X18 @ X17)
% 3.37/3.59          | ~ (v2_struct_0 @ (k1_tsep_1 @ X17 @ X16 @ X18)))),
% 3.37/3.59      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 3.37/3.59  thf('240', plain,
% 3.37/3.59      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | ~ (l1_pre_topc @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | ~ (m1_pre_topc @ sk_C @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['238', '239'])).
% 3.37/3.59  thf('241', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('242', plain, ((l1_pre_topc @ sk_C)),
% 3.37/3.59      inference('demod', [status(thm)], ['166', '167'])).
% 3.37/3.59  thf('243', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.37/3.59      inference('sup-', [status(thm)], ['151', '169'])).
% 3.37/3.59  thf('244', plain,
% 3.37/3.59      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['240', '241', '242', '243'])).
% 3.37/3.59  thf('245', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | (v2_struct_0 @ sk_D)
% 3.37/3.59        | ~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C)))),
% 3.37/3.59      inference('simplify', [status(thm)], ['244'])).
% 3.37/3.59  thf('246', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('247', plain,
% 3.37/3.59      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('clc', [status(thm)], ['245', '246'])).
% 3.37/3.59  thf('248', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('249', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['247', '248'])).
% 3.37/3.59  thf('250', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['237', '249'])).
% 3.37/3.59  thf('251', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('252', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59            = (u1_struct_0 @ sk_C)))),
% 3.37/3.59      inference('clc', [status(thm)], ['250', '251'])).
% 3.37/3.59  thf('253', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('254', plain,
% 3.37/3.59      (((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C)) = (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['252', '253'])).
% 3.37/3.59  thf('255', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | ((u1_struct_0 @ sk_C)
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 3.37/3.59        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['215', '254'])).
% 3.37/3.59  thf('256', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_D @ sk_C))),
% 3.37/3.59      inference('clc', [status(thm)], ['247', '248'])).
% 3.37/3.59  thf('257', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_C)
% 3.37/3.59        | ((u1_struct_0 @ sk_C)
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('sup-', [status(thm)], ['255', '256'])).
% 3.37/3.59  thf('258', plain, (~ (v2_struct_0 @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('259', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | ((u1_struct_0 @ sk_C)
% 3.37/3.59            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))),
% 3.37/3.59      inference('clc', [status(thm)], ['257', '258'])).
% 3.37/3.59  thf('260', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('261', plain,
% 3.37/3.59      (((u1_struct_0 @ sk_C)
% 3.37/3.59         = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 3.37/3.59      inference('clc', [status(thm)], ['259', '260'])).
% 3.37/3.59  thf('262', plain,
% 3.37/3.59      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['72', '73'])).
% 3.37/3.59  thf('263', plain,
% 3.37/3.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.37/3.59         (~ (r1_tarski @ X2 @ X3)
% 3.37/3.59          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ (k2_xboole_0 @ X3 @ X4)))),
% 3.37/3.59      inference('cnf', [status(esa)], [t9_xboole_1])).
% 3.37/3.59  thf('264', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (r1_tarski @ (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0) @ 
% 3.37/3.59          (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ X0))),
% 3.37/3.59      inference('sup-', [status(thm)], ['262', '263'])).
% 3.37/3.59  thf('265', plain,
% 3.37/3.59      ((r1_tarski @ 
% 3.37/3.59        (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 3.37/3.59        (u1_struct_0 @ sk_C))),
% 3.37/3.59      inference('sup+', [status(thm)], ['261', '264'])).
% 3.37/3.59  thf('266', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_B)
% 3.37/3.59        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 3.37/3.59           (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 3.37/3.59      inference('demod', [status(thm)], ['138', '265'])).
% 3.37/3.59  thf('267', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_B)
% 3.37/3.59        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 3.37/3.59           (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_B)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('sup-', [status(thm)], ['7', '266'])).
% 3.37/3.59  thf('268', plain,
% 3.37/3.59      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 3.37/3.59         (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59        | (v2_struct_0 @ sk_B)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('simplify', [status(thm)], ['267'])).
% 3.37/3.59  thf('269', plain,
% 3.37/3.59      (![X0 : $i]:
% 3.37/3.59         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 3.37/3.59          | (m1_pre_topc @ X0 @ sk_C))),
% 3.37/3.59      inference('demod', [status(thm)], ['163', '168'])).
% 3.37/3.59  thf('270', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_D)
% 3.37/3.59        | (v2_struct_0 @ sk_A)
% 3.37/3.59        | (v2_struct_0 @ sk_B)
% 3.37/3.59        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))),
% 3.37/3.59      inference('sup-', [status(thm)], ['268', '269'])).
% 3.37/3.59  thf('271', plain,
% 3.37/3.59      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('272', plain,
% 3.37/3.59      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 3.37/3.59      inference('sup-', [status(thm)], ['270', '271'])).
% 3.37/3.59  thf('273', plain, (~ (v2_struct_0 @ sk_B)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('274', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 3.37/3.59      inference('clc', [status(thm)], ['272', '273'])).
% 3.37/3.59  thf('275', plain, (~ (v2_struct_0 @ sk_D)),
% 3.37/3.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.59  thf('276', plain, ((v2_struct_0 @ sk_A)),
% 3.37/3.59      inference('clc', [status(thm)], ['274', '275'])).
% 3.37/3.59  thf('277', plain, ($false), inference('demod', [status(thm)], ['0', '276'])).
% 3.37/3.59  
% 3.37/3.59  % SZS output end Refutation
% 3.37/3.59  
% 3.37/3.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
