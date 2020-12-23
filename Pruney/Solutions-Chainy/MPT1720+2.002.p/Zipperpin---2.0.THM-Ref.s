%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Afj14ZLEI7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:28 EST 2020

% Result     : Theorem 9.64s
% Output     : Refutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :  299 (14484 expanded)
%              Number of leaves         :   25 (3968 expanded)
%              Depth                    :   48
%              Number of atoms          : 3285 (242622 expanded)
%              Number of equality atoms :   56 (1635 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) @ X16 ) ) ),
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
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ X0 ) @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ X0 ) @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','24'])).

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

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( X13
       != ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ( ( u1_struct_0 @ X13 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) @ X12 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_C )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

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

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ( m1_pre_topc @ X20 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

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

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k1_tsep_1 @ X19 @ X18 @ X18 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('58',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','61','62'])).

thf('64',plain,
    ( ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','68'])).

thf('70',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('72',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('75',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('79',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('82',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k1_tsep_1 @ X19 @ X18 @ X18 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('87',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('90',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ X0 ) @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ X0 ) @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ X0 ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('100',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('102',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('103',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['96','97'])).

thf('105',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('108',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('110',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
      = ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['87','103','108','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k1_tsep_1 @ X19 @ X18 @ X18 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('122',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('124',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
      = ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['110','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) @ X12 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('138',plain,
    ( ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['96','97'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('141',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('143',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('144',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('146',plain,
    ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('147',plain,
    ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('148',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('149',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('150',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k1_tsep_1 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C @ sk_C )
    = ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('160',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('161',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','144','145','146','147','158','159','160','161'])).

thf('163',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('169',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('170',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('173',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ~ ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['168','174'])).

thf('176',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('177',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('179',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('181',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['96','97'])).

thf('183',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['96','97'])).

thf('184',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('187',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['182','190'])).

thf('192',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('193',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['181','193'])).

thf('195',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['167','194'])).

thf('196',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['96','97'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','195','196'])).

thf('198',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['35','198'])).

thf('200',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['201','206'])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('209',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) @ X12 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('210',plain,
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
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
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
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['207','215'])).

thf('217',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['218','223'])).

thf('225',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['167','194'])).

thf('233',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ( m1_pre_topc @ X20 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) @ X1 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['231','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['217','238'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['200','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','241'])).

thf('243',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('245',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['243','248'])).

thf('250',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['253','254','255','256'])).

thf('258',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('263',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['269','270'])).

thf('272',plain,(
    $false ),
    inference(demod,[status(thm)],['0','271'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Afj14ZLEI7
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:53:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 9.64/9.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.64/9.81  % Solved by: fo/fo7.sh
% 9.64/9.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.64/9.81  % done 6373 iterations in 9.366s
% 9.64/9.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.64/9.81  % SZS output start Refutation
% 9.64/9.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.64/9.81  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 9.64/9.81  thf(sk_D_type, type, sk_D: $i).
% 9.64/9.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 9.64/9.81  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 9.64/9.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.64/9.81  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 9.64/9.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.64/9.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 9.64/9.81  thf(sk_C_type, type, sk_C: $i).
% 9.64/9.81  thf(sk_A_type, type, sk_A: $i).
% 9.64/9.81  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 9.64/9.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.64/9.81  thf(sk_B_type, type, sk_B: $i).
% 9.64/9.81  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 9.64/9.81  thf(t29_tmap_1, conjecture,
% 9.64/9.81    (![A:$i]:
% 9.64/9.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.64/9.81       ( ![B:$i]:
% 9.64/9.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 9.64/9.81           ( ![C:$i]:
% 9.64/9.81             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 9.64/9.81               ( ![D:$i]:
% 9.64/9.81                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 9.64/9.81                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 9.64/9.81                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 9.64/9.81  thf(zf_stmt_0, negated_conjecture,
% 9.64/9.81    (~( ![A:$i]:
% 9.64/9.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 9.64/9.81            ( l1_pre_topc @ A ) ) =>
% 9.64/9.81          ( ![B:$i]:
% 9.64/9.81            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 9.64/9.81              ( ![C:$i]:
% 9.64/9.81                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 9.64/9.81                  ( ![D:$i]:
% 9.64/9.81                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 9.64/9.81                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 9.64/9.81                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 9.64/9.81    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 9.64/9.81  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf(dt_k1_tsep_1, axiom,
% 9.64/9.81    (![A:$i,B:$i,C:$i]:
% 9.64/9.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 9.64/9.81         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 9.64/9.81         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 9.64/9.81       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 9.64/9.81         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 9.64/9.81         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 9.64/9.81  thf('3', plain,
% 9.64/9.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.81         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.81          | (v2_struct_0 @ X15)
% 9.64/9.81          | ~ (l1_pre_topc @ X16)
% 9.64/9.81          | (v2_struct_0 @ X16)
% 9.64/9.81          | (v2_struct_0 @ X17)
% 9.64/9.81          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.81          | (m1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17) @ X16))),
% 9.64/9.81      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.81  thf('4', plain,
% 9.64/9.81      (![X0 : $i]:
% 9.64/9.81         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 9.64/9.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.81          | (v2_struct_0 @ X0)
% 9.64/9.81          | (v2_struct_0 @ sk_A)
% 9.64/9.81          | ~ (l1_pre_topc @ sk_A)
% 9.64/9.81          | (v2_struct_0 @ sk_B))),
% 9.64/9.81      inference('sup-', [status(thm)], ['2', '3'])).
% 9.64/9.81  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf('6', plain,
% 9.64/9.81      (![X0 : $i]:
% 9.64/9.81         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 9.64/9.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.81          | (v2_struct_0 @ X0)
% 9.64/9.81          | (v2_struct_0 @ sk_A)
% 9.64/9.81          | (v2_struct_0 @ sk_B))),
% 9.64/9.81      inference('demod', [status(thm)], ['4', '5'])).
% 9.64/9.81  thf('7', plain,
% 9.64/9.81      (((v2_struct_0 @ sk_B)
% 9.64/9.81        | (v2_struct_0 @ sk_A)
% 9.64/9.81        | (v2_struct_0 @ sk_D)
% 9.64/9.81        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 9.64/9.81      inference('sup-', [status(thm)], ['1', '6'])).
% 9.64/9.81  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf('10', plain,
% 9.64/9.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.81         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.81          | (v2_struct_0 @ X15)
% 9.64/9.81          | ~ (l1_pre_topc @ X16)
% 9.64/9.81          | (v2_struct_0 @ X16)
% 9.64/9.81          | (v2_struct_0 @ X17)
% 9.64/9.81          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.81          | (v1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17)))),
% 9.64/9.81      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.81  thf('11', plain,
% 9.64/9.81      (![X0 : $i]:
% 9.64/9.81         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 9.64/9.81          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.81          | (v2_struct_0 @ X0)
% 9.64/9.81          | (v2_struct_0 @ sk_C)
% 9.64/9.81          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.81          | (v2_struct_0 @ sk_B))),
% 9.64/9.81      inference('sup-', [status(thm)], ['9', '10'])).
% 9.64/9.81  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf(dt_m1_pre_topc, axiom,
% 9.64/9.81    (![A:$i]:
% 9.64/9.81     ( ( l1_pre_topc @ A ) =>
% 9.64/9.81       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 9.64/9.81  thf('13', plain,
% 9.64/9.81      (![X5 : $i, X6 : $i]:
% 9.64/9.81         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.64/9.81      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.64/9.81  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 9.64/9.81      inference('sup-', [status(thm)], ['12', '13'])).
% 9.64/9.81  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.81  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.81      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.81  thf('17', plain,
% 9.64/9.81      (![X0 : $i]:
% 9.64/9.81         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 9.64/9.81          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.81          | (v2_struct_0 @ X0)
% 9.64/9.81          | (v2_struct_0 @ sk_C)
% 9.64/9.81          | (v2_struct_0 @ sk_B))),
% 9.64/9.81      inference('demod', [status(thm)], ['11', '16'])).
% 9.64/9.81  thf('18', plain,
% 9.64/9.81      (((v2_struct_0 @ sk_B)
% 9.64/9.81        | (v2_struct_0 @ sk_C)
% 9.64/9.81        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['8', '17'])).
% 9.64/9.82  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('21', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | (m1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17) @ X16))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('22', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('sup-', [status(thm)], ['20', '21'])).
% 9.64/9.82  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('24', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('demod', [status(thm)], ['22', '23'])).
% 9.64/9.82  thf('25', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['19', '24'])).
% 9.64/9.82  thf(d2_tsep_1, axiom,
% 9.64/9.82    (![A:$i]:
% 9.64/9.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 9.64/9.82       ( ![B:$i]:
% 9.64/9.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 9.64/9.82           ( ![C:$i]:
% 9.64/9.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 9.64/9.82               ( ![D:$i]:
% 9.64/9.82                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 9.64/9.82                     ( m1_pre_topc @ D @ A ) ) =>
% 9.64/9.82                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 9.64/9.82                     ( ( u1_struct_0 @ D ) =
% 9.64/9.82                       ( k2_xboole_0 @
% 9.64/9.82                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 9.64/9.82  thf('26', plain,
% 9.64/9.82      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X11)
% 9.64/9.82          | ~ (m1_pre_topc @ X11 @ X12)
% 9.64/9.82          | (v2_struct_0 @ X13)
% 9.64/9.82          | ~ (v1_pre_topc @ X13)
% 9.64/9.82          | ~ (m1_pre_topc @ X13 @ X12)
% 9.64/9.82          | ((X13) != (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | ((u1_struct_0 @ X13)
% 9.64/9.82              = (k2_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X14)))
% 9.64/9.82          | ~ (m1_pre_topc @ X14 @ X12)
% 9.64/9.82          | (v2_struct_0 @ X14)
% 9.64/9.82          | ~ (l1_pre_topc @ X12)
% 9.64/9.82          | (v2_struct_0 @ X12))),
% 9.64/9.82      inference('cnf', [status(esa)], [d2_tsep_1])).
% 9.64/9.82  thf('27', plain,
% 9.64/9.82      (![X11 : $i, X12 : $i, X14 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X12)
% 9.64/9.82          | ~ (l1_pre_topc @ X12)
% 9.64/9.82          | (v2_struct_0 @ X14)
% 9.64/9.82          | ~ (m1_pre_topc @ X14 @ X12)
% 9.64/9.82          | ((u1_struct_0 @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82              = (k2_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X14)))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ X12 @ X11 @ X14) @ X12)
% 9.64/9.82          | ~ (v1_pre_topc @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | (v2_struct_0 @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | ~ (m1_pre_topc @ X11 @ X12)
% 9.64/9.82          | (v2_struct_0 @ X11))),
% 9.64/9.82      inference('simplify', [status(thm)], ['26'])).
% 9.64/9.82  thf('28', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['25', '27'])).
% 9.64/9.82  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('32', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 9.64/9.82  thf('33', plain,
% 9.64/9.82      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['32'])).
% 9.64/9.82  thf('34', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 9.64/9.82      inference('sup-', [status(thm)], ['18', '33'])).
% 9.64/9.82  thf('35', plain,
% 9.64/9.82      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['34'])).
% 9.64/9.82  thf('36', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['19', '24'])).
% 9.64/9.82  thf('37', plain,
% 9.64/9.82      (![X5 : $i, X6 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.64/9.82  thf('38', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['36', '37'])).
% 9.64/9.82  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('40', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)))),
% 9.64/9.82      inference('demod', [status(thm)], ['38', '39'])).
% 9.64/9.82  thf('41', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['19', '24'])).
% 9.64/9.82  thf(t65_pre_topc, axiom,
% 9.64/9.82    (![A:$i]:
% 9.64/9.82     ( ( l1_pre_topc @ A ) =>
% 9.64/9.82       ( ![B:$i]:
% 9.64/9.82         ( ( l1_pre_topc @ B ) =>
% 9.64/9.82           ( ( m1_pre_topc @ A @ B ) <=>
% 9.64/9.82             ( m1_pre_topc @
% 9.64/9.82               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 9.64/9.82  thf('42', plain,
% 9.64/9.82      (![X9 : $i, X10 : $i]:
% 9.64/9.82         (~ (l1_pre_topc @ X9)
% 9.64/9.82          | ~ (m1_pre_topc @ X10 @ X9)
% 9.64/9.82          | (m1_pre_topc @ X10 @ 
% 9.64/9.82             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 9.64/9.82          | ~ (l1_pre_topc @ X10))),
% 9.64/9.82      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.64/9.82  thf('43', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ 
% 9.64/9.82           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['41', '42'])).
% 9.64/9.82  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf(d10_xboole_0, axiom,
% 9.64/9.82    (![A:$i,B:$i]:
% 9.64/9.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.64/9.82  thf('45', plain,
% 9.64/9.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.64/9.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.64/9.82  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.64/9.82      inference('simplify', [status(thm)], ['45'])).
% 9.64/9.82  thf(t4_tsep_1, axiom,
% 9.64/9.82    (![A:$i]:
% 9.64/9.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.64/9.82       ( ![B:$i]:
% 9.64/9.82         ( ( m1_pre_topc @ B @ A ) =>
% 9.64/9.82           ( ![C:$i]:
% 9.64/9.82             ( ( m1_pre_topc @ C @ A ) =>
% 9.64/9.82               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 9.64/9.82                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 9.64/9.82  thf('47', plain,
% 9.64/9.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X20 @ X21)
% 9.64/9.82          | ~ (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 9.64/9.82          | (m1_pre_topc @ X20 @ X22)
% 9.64/9.82          | ~ (m1_pre_topc @ X22 @ X21)
% 9.64/9.82          | ~ (l1_pre_topc @ X21)
% 9.64/9.82          | ~ (v2_pre_topc @ X21))),
% 9.64/9.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 9.64/9.82  thf('48', plain,
% 9.64/9.82      (![X0 : $i, X1 : $i]:
% 9.64/9.82         (~ (v2_pre_topc @ X1)
% 9.64/9.82          | ~ (l1_pre_topc @ X1)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ X1)
% 9.64/9.82          | (m1_pre_topc @ X0 @ X0)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ X1))),
% 9.64/9.82      inference('sup-', [status(thm)], ['46', '47'])).
% 9.64/9.82  thf('49', plain,
% 9.64/9.82      (![X0 : $i, X1 : $i]:
% 9.64/9.82         ((m1_pre_topc @ X0 @ X0)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ X1)
% 9.64/9.82          | ~ (l1_pre_topc @ X1)
% 9.64/9.82          | ~ (v2_pre_topc @ X1))),
% 9.64/9.82      inference('simplify', [status(thm)], ['48'])).
% 9.64/9.82  thf('50', plain,
% 9.64/9.82      ((~ (v2_pre_topc @ sk_A)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82        | (m1_pre_topc @ sk_C @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['44', '49'])).
% 9.64/9.82  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf(t25_tmap_1, axiom,
% 9.64/9.82    (![A:$i]:
% 9.64/9.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.64/9.82       ( ![B:$i]:
% 9.64/9.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 9.64/9.82           ( ( k1_tsep_1 @ A @ B @ B ) =
% 9.64/9.82             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 9.64/9.82  thf('54', plain,
% 9.64/9.82      (![X18 : $i, X19 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X18)
% 9.64/9.82          | ~ (m1_pre_topc @ X18 @ X19)
% 9.64/9.82          | ((k1_tsep_1 @ X19 @ X18 @ X18)
% 9.64/9.82              = (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 9.64/9.82          | ~ (l1_pre_topc @ X19)
% 9.64/9.82          | ~ (v2_pre_topc @ X19)
% 9.64/9.82          | (v2_struct_0 @ X19))),
% 9.64/9.82      inference('cnf', [status(esa)], [t25_tmap_1])).
% 9.64/9.82  thf('55', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (v2_pre_topc @ sk_C)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | ((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['53', '54'])).
% 9.64/9.82  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf(cc1_pre_topc, axiom,
% 9.64/9.82    (![A:$i]:
% 9.64/9.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.64/9.82       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 9.64/9.82  thf('57', plain,
% 9.64/9.82      (![X3 : $i, X4 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X3 @ X4)
% 9.64/9.82          | (v2_pre_topc @ X3)
% 9.64/9.82          | ~ (l1_pre_topc @ X4)
% 9.64/9.82          | ~ (v2_pre_topc @ X4))),
% 9.64/9.82      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 9.64/9.82  thf('58', plain,
% 9.64/9.82      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['56', '57'])).
% 9.64/9.82  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('61', plain, ((v2_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['58', '59', '60'])).
% 9.64/9.82  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('63', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | ((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['55', '61', '62'])).
% 9.64/9.82  thf('64', plain,
% 9.64/9.82      ((((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82          = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('simplify', [status(thm)], ['63'])).
% 9.64/9.82  thf('65', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('66', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['64', '65'])).
% 9.64/9.82  thf('67', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('68', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('demod', [status(thm)], ['43', '66', '67'])).
% 9.64/9.82  thf('69', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('sup-', [status(thm)], ['40', '68'])).
% 9.64/9.82  thf('70', plain,
% 9.64/9.82      (((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ 
% 9.64/9.82         (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('simplify', [status(thm)], ['69'])).
% 9.64/9.82  thf('71', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['19', '24'])).
% 9.64/9.82  thf('72', plain,
% 9.64/9.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X20 @ X21)
% 9.64/9.82          | ~ (m1_pre_topc @ X20 @ X22)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 9.64/9.82          | ~ (m1_pre_topc @ X22 @ X21)
% 9.64/9.82          | ~ (l1_pre_topc @ X21)
% 9.64/9.82          | ~ (v2_pre_topc @ X21))),
% 9.64/9.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 9.64/9.82  thf('73', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v2_struct_0 @ sk_D)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_B)
% 9.64/9.82          | ~ (v2_pre_topc @ sk_C)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 9.64/9.82             (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ X0))),
% 9.64/9.82      inference('sup-', [status(thm)], ['71', '72'])).
% 9.64/9.82  thf('74', plain, ((v2_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['58', '59', '60'])).
% 9.64/9.82  thf('75', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('76', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v2_struct_0 @ sk_D)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_B)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 9.64/9.82             (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ X0))),
% 9.64/9.82      inference('demod', [status(thm)], ['73', '74', '75'])).
% 9.64/9.82  thf('77', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 9.64/9.82           (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))
% 9.64/9.82        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('sup-', [status(thm)], ['70', '76'])).
% 9.64/9.82  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf('79', plain,
% 9.64/9.82      (![X9 : $i, X10 : $i]:
% 9.64/9.82         (~ (l1_pre_topc @ X9)
% 9.64/9.82          | ~ (m1_pre_topc @ X10 @ X9)
% 9.64/9.82          | (m1_pre_topc @ X10 @ 
% 9.64/9.82             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 9.64/9.82          | ~ (l1_pre_topc @ X10))),
% 9.64/9.82      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.64/9.82  thf('80', plain,
% 9.64/9.82      ((~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (m1_pre_topc @ sk_C @ 
% 9.64/9.82           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['78', '79'])).
% 9.64/9.82  thf('81', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('82', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('83', plain,
% 9.64/9.82      ((m1_pre_topc @ sk_C @ 
% 9.64/9.82        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('demod', [status(thm)], ['80', '81', '82'])).
% 9.64/9.82  thf('84', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['64', '65'])).
% 9.64/9.82  thf('85', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['83', '84'])).
% 9.64/9.82  thf('86', plain,
% 9.64/9.82      (![X18 : $i, X19 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X18)
% 9.64/9.82          | ~ (m1_pre_topc @ X18 @ X19)
% 9.64/9.82          | ((k1_tsep_1 @ X19 @ X18 @ X18)
% 9.64/9.82              = (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 9.64/9.82          | ~ (l1_pre_topc @ X19)
% 9.64/9.82          | ~ (v2_pre_topc @ X19)
% 9.64/9.82          | (v2_struct_0 @ X19))),
% 9.64/9.82      inference('cnf', [status(esa)], [t25_tmap_1])).
% 9.64/9.82  thf('87', plain,
% 9.64/9.82      (((v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['85', '86'])).
% 9.64/9.82  thf('88', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf('90', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | (m1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17) @ X16))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('91', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ X0) @ sk_C)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['89', '90'])).
% 9.64/9.82  thf('92', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('93', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ X0) @ sk_C)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['91', '92'])).
% 9.64/9.82  thf('94', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ X0) @ sk_C))),
% 9.64/9.82      inference('simplify', [status(thm)], ['93'])).
% 9.64/9.82  thf('95', plain,
% 9.64/9.82      (((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['88', '94'])).
% 9.64/9.82  thf('96', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C))),
% 9.64/9.82      inference('simplify', [status(thm)], ['95'])).
% 9.64/9.82  thf('97', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('98', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)),
% 9.64/9.82      inference('clc', [status(thm)], ['96', '97'])).
% 9.64/9.82  thf('99', plain,
% 9.64/9.82      (![X3 : $i, X4 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X3 @ X4)
% 9.64/9.82          | (v2_pre_topc @ X3)
% 9.64/9.82          | ~ (l1_pre_topc @ X4)
% 9.64/9.82          | ~ (v2_pre_topc @ X4))),
% 9.64/9.82      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 9.64/9.82  thf('100', plain,
% 9.64/9.82      ((~ (v2_pre_topc @ sk_C)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (v2_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['98', '99'])).
% 9.64/9.82  thf('101', plain, ((v2_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['58', '59', '60'])).
% 9.64/9.82  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('103', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['100', '101', '102'])).
% 9.64/9.82  thf('104', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)),
% 9.64/9.82      inference('clc', [status(thm)], ['96', '97'])).
% 9.64/9.82  thf('105', plain,
% 9.64/9.82      (![X5 : $i, X6 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.64/9.82  thf('106', plain,
% 9.64/9.82      ((~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['104', '105'])).
% 9.64/9.82  thf('107', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('108', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['106', '107'])).
% 9.64/9.82  thf('109', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['64', '65'])).
% 9.64/9.82  thf('110', plain,
% 9.64/9.82      (((v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82            = (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['87', '103', '108', '109'])).
% 9.64/9.82  thf('111', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('112', plain,
% 9.64/9.82      (![X18 : $i, X19 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X18)
% 9.64/9.82          | ~ (m1_pre_topc @ X18 @ X19)
% 9.64/9.82          | ((k1_tsep_1 @ X19 @ X18 @ X18)
% 9.64/9.82              = (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 9.64/9.82          | ~ (l1_pre_topc @ X19)
% 9.64/9.82          | ~ (v2_pre_topc @ X19)
% 9.64/9.82          | (v2_struct_0 @ X19))),
% 9.64/9.82      inference('cnf', [status(esa)], [t25_tmap_1])).
% 9.64/9.82  thf('113', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_A)
% 9.64/9.82        | ~ (v2_pre_topc @ sk_A)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 9.64/9.82            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['111', '112'])).
% 9.64/9.82  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('116', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_A)
% 9.64/9.82        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 9.64/9.82            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['113', '114', '115'])).
% 9.64/9.82  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('118', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 9.64/9.82            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 9.64/9.82      inference('clc', [status(thm)], ['116', '117'])).
% 9.64/9.82  thf('119', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('120', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 9.64/9.82         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['118', '119'])).
% 9.64/9.82  thf('121', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['64', '65'])).
% 9.64/9.82  thf('122', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 9.64/9.82      inference('sup+', [status(thm)], ['120', '121'])).
% 9.64/9.82  thf('123', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | ~ (v2_struct_0 @ (k1_tsep_1 @ X16 @ X15 @ X17)))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('124', plain,
% 9.64/9.82      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['122', '123'])).
% 9.64/9.82  thf('125', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('127', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('128', plain,
% 9.64/9.82      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 9.64/9.82  thf('129', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('simplify', [status(thm)], ['128'])).
% 9.64/9.82  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('131', plain,
% 9.64/9.82      ((~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['129', '130'])).
% 9.64/9.82  thf('132', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('133', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['131', '132'])).
% 9.64/9.82  thf('134', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | ((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82            = (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['110', '133'])).
% 9.64/9.82  thf('135', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('136', plain,
% 9.64/9.82      (((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82         = (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['134', '135'])).
% 9.64/9.82  thf('137', plain,
% 9.64/9.82      (![X11 : $i, X12 : $i, X14 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X12)
% 9.64/9.82          | ~ (l1_pre_topc @ X12)
% 9.64/9.82          | (v2_struct_0 @ X14)
% 9.64/9.82          | ~ (m1_pre_topc @ X14 @ X12)
% 9.64/9.82          | ((u1_struct_0 @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82              = (k2_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X14)))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ X12 @ X11 @ X14) @ X12)
% 9.64/9.82          | ~ (v1_pre_topc @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | (v2_struct_0 @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | ~ (m1_pre_topc @ X11 @ X12)
% 9.64/9.82          | (v2_struct_0 @ X11))),
% 9.64/9.82      inference('simplify', [status(thm)], ['26'])).
% 9.64/9.82  thf('138', plain,
% 9.64/9.82      ((~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ 
% 9.64/9.82           (k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C))
% 9.64/9.82        | ~ (v1_pre_topc @ 
% 9.64/9.82             (k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C))
% 9.64/9.82        | ((u1_struct_0 @ 
% 9.64/9.82            (k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 9.64/9.82        | ~ (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['136', '137'])).
% 9.64/9.82  thf('139', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)),
% 9.64/9.82      inference('clc', [status(thm)], ['96', '97'])).
% 9.64/9.82  thf('140', plain,
% 9.64/9.82      (![X0 : $i, X1 : $i]:
% 9.64/9.82         ((m1_pre_topc @ X0 @ X0)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ X1)
% 9.64/9.82          | ~ (l1_pre_topc @ X1)
% 9.64/9.82          | ~ (v2_pre_topc @ X1))),
% 9.64/9.82      inference('simplify', [status(thm)], ['48'])).
% 9.64/9.82  thf('141', plain,
% 9.64/9.82      ((~ (v2_pre_topc @ sk_C)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['139', '140'])).
% 9.64/9.82  thf('142', plain, ((v2_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['58', '59', '60'])).
% 9.64/9.82  thf('143', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('144', plain,
% 9.64/9.82      ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ 
% 9.64/9.82        (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['141', '142', '143'])).
% 9.64/9.82  thf('145', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['83', '84'])).
% 9.64/9.82  thf('146', plain,
% 9.64/9.82      (((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82         = (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['134', '135'])).
% 9.64/9.82  thf('147', plain,
% 9.64/9.82      (((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82         = (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['134', '135'])).
% 9.64/9.82  thf('148', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf('149', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf('150', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | (v1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17)))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('151', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['149', '150'])).
% 9.64/9.82  thf('152', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('153', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['151', '152'])).
% 9.64/9.82  thf('154', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v2_struct_0 @ sk_C)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ X0)))),
% 9.64/9.82      inference('simplify', [status(thm)], ['153'])).
% 9.64/9.82  thf('155', plain,
% 9.64/9.82      (((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['148', '154'])).
% 9.64/9.82  thf('156', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C) | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('simplify', [status(thm)], ['155'])).
% 9.64/9.82  thf('157', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('158', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['156', '157'])).
% 9.64/9.82  thf('159', plain,
% 9.64/9.82      (((k1_tsep_1 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C @ sk_C)
% 9.64/9.82         = (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['134', '135'])).
% 9.64/9.82  thf('160', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['83', '84'])).
% 9.64/9.82  thf('161', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['106', '107'])).
% 9.64/9.82  thf('162', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('demod', [status(thm)],
% 9.64/9.82                ['138', '144', '145', '146', '147', '158', '159', '160', '161'])).
% 9.64/9.82  thf('163', plain,
% 9.64/9.82      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('simplify', [status(thm)], ['162'])).
% 9.64/9.82  thf('164', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('clc', [status(thm)], ['131', '132'])).
% 9.64/9.82  thf('165', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))))),
% 9.64/9.82      inference('clc', [status(thm)], ['163', '164'])).
% 9.64/9.82  thf('166', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('167', plain,
% 9.64/9.82      (((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82         = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['165', '166'])).
% 9.64/9.82  thf('168', plain,
% 9.64/9.82      ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ 
% 9.64/9.82        (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['141', '142', '143'])).
% 9.64/9.82  thf('169', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['83', '84'])).
% 9.64/9.82  thf('170', plain,
% 9.64/9.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X20 @ X21)
% 9.64/9.82          | ~ (m1_pre_topc @ X20 @ X22)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 9.64/9.82          | ~ (m1_pre_topc @ X22 @ X21)
% 9.64/9.82          | ~ (l1_pre_topc @ X21)
% 9.64/9.82          | ~ (v2_pre_topc @ X21))),
% 9.64/9.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 9.64/9.82  thf('171', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 9.64/9.82      inference('sup-', [status(thm)], ['169', '170'])).
% 9.64/9.82  thf('172', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['100', '101', '102'])).
% 9.64/9.82  thf('173', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['106', '107'])).
% 9.64/9.82  thf('174', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 9.64/9.82      inference('demod', [status(thm)], ['171', '172', '173'])).
% 9.64/9.82  thf('175', plain,
% 9.64/9.82      ((~ (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 9.64/9.82           (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))))),
% 9.64/9.82      inference('sup-', [status(thm)], ['168', '174'])).
% 9.64/9.82  thf('176', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['83', '84'])).
% 9.64/9.82  thf('177', plain,
% 9.64/9.82      ((r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 9.64/9.82        (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 9.64/9.82      inference('demod', [status(thm)], ['175', '176'])).
% 9.64/9.82  thf('178', plain,
% 9.64/9.82      (((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82         = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['165', '166'])).
% 9.64/9.82  thf('179', plain,
% 9.64/9.82      ((r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 9.64/9.82        (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('demod', [status(thm)], ['177', '178'])).
% 9.64/9.82  thf('180', plain,
% 9.64/9.82      (![X0 : $i, X2 : $i]:
% 9.64/9.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.64/9.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.64/9.82  thf('181', plain,
% 9.64/9.82      ((~ (r1_tarski @ 
% 9.64/9.82           (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)) @ 
% 9.64/9.82           (u1_struct_0 @ sk_C))
% 9.64/9.82        | ((k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 9.64/9.82            = (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['179', '180'])).
% 9.64/9.82  thf('182', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)),
% 9.64/9.82      inference('clc', [status(thm)], ['96', '97'])).
% 9.64/9.82  thf('183', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)),
% 9.64/9.82      inference('clc', [status(thm)], ['96', '97'])).
% 9.64/9.82  thf('184', plain,
% 9.64/9.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X20 @ X21)
% 9.64/9.82          | ~ (m1_pre_topc @ X20 @ X22)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 9.64/9.82          | ~ (m1_pre_topc @ X22 @ X21)
% 9.64/9.82          | ~ (l1_pre_topc @ X21)
% 9.64/9.82          | ~ (v2_pre_topc @ X21))),
% 9.64/9.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 9.64/9.82  thf('185', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (v2_pre_topc @ sk_C)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)) @ 
% 9.64/9.82             (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ X0))),
% 9.64/9.82      inference('sup-', [status(thm)], ['183', '184'])).
% 9.64/9.82  thf('186', plain, ((v2_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['58', '59', '60'])).
% 9.64/9.82  thf('187', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('188', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)) @ 
% 9.64/9.82             (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ X0))),
% 9.64/9.82      inference('demod', [status(thm)], ['185', '186', '187'])).
% 9.64/9.82  thf('189', plain,
% 9.64/9.82      (((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82         = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['165', '166'])).
% 9.64/9.82  thf('190', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ sk_C)
% 9.64/9.82          | (r1_tarski @ 
% 9.64/9.82             (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)) @ 
% 9.64/9.82             (u1_struct_0 @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ X0))),
% 9.64/9.82      inference('demod', [status(thm)], ['188', '189'])).
% 9.64/9.82  thf('191', plain,
% 9.64/9.82      (((r1_tarski @ 
% 9.64/9.82         (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)) @ 
% 9.64/9.82         (u1_struct_0 @ sk_C))
% 9.64/9.82        | ~ (m1_pre_topc @ sk_C @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['182', '190'])).
% 9.64/9.82  thf('192', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 9.64/9.82  thf('193', plain,
% 9.64/9.82      ((r1_tarski @ 
% 9.64/9.82        (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)) @ 
% 9.64/9.82        (u1_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['191', '192'])).
% 9.64/9.82  thf('194', plain,
% 9.64/9.82      (((k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 9.64/9.82         = (u1_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['181', '193'])).
% 9.64/9.82  thf('195', plain,
% 9.64/9.82      (((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)) = (u1_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['167', '194'])).
% 9.64/9.82  thf('196', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_C)),
% 9.64/9.82      inference('clc', [status(thm)], ['96', '97'])).
% 9.64/9.82  thf('197', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 9.64/9.82           (u1_struct_0 @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('demod', [status(thm)], ['77', '195', '196'])).
% 9.64/9.82  thf('198', plain,
% 9.64/9.82      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 9.64/9.82         (u1_struct_0 @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('simplify', [status(thm)], ['197'])).
% 9.64/9.82  thf('199', plain,
% 9.64/9.82      (((r1_tarski @ 
% 9.64/9.82         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 9.64/9.82         (u1_struct_0 @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('sup+', [status(thm)], ['35', '198'])).
% 9.64/9.82  thf('200', plain,
% 9.64/9.82      (((v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (r1_tarski @ 
% 9.64/9.82           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 9.64/9.82           (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('simplify', [status(thm)], ['199'])).
% 9.64/9.82  thf('201', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('202', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('203', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | (v1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17)))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('204', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_A)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('sup-', [status(thm)], ['202', '203'])).
% 9.64/9.82  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('206', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('demod', [status(thm)], ['204', '205'])).
% 9.64/9.82  thf('207', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['201', '206'])).
% 9.64/9.82  thf('208', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['1', '6'])).
% 9.64/9.82  thf('209', plain,
% 9.64/9.82      (![X11 : $i, X12 : $i, X14 : $i]:
% 9.64/9.82         ((v2_struct_0 @ X12)
% 9.64/9.82          | ~ (l1_pre_topc @ X12)
% 9.64/9.82          | (v2_struct_0 @ X14)
% 9.64/9.82          | ~ (m1_pre_topc @ X14 @ X12)
% 9.64/9.82          | ((u1_struct_0 @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82              = (k2_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X14)))
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ X12 @ X11 @ X14) @ X12)
% 9.64/9.82          | ~ (v1_pre_topc @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | (v2_struct_0 @ (k1_tsep_1 @ X12 @ X11 @ X14))
% 9.64/9.82          | ~ (m1_pre_topc @ X11 @ X12)
% 9.64/9.82          | (v2_struct_0 @ X11))),
% 9.64/9.82      inference('simplify', [status(thm)], ['26'])).
% 9.64/9.82  thf('210', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['208', '209'])).
% 9.64/9.82  thf('211', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('212', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('214', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A))),
% 9.64/9.82      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 9.64/9.82  thf('215', plain,
% 9.64/9.82      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['214'])).
% 9.64/9.82  thf('216', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 9.64/9.82      inference('sup-', [status(thm)], ['207', '215'])).
% 9.64/9.82  thf('217', plain,
% 9.64/9.82      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['216'])).
% 9.64/9.82  thf('218', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('219', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('220', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | (m1_pre_topc @ (k1_tsep_1 @ X16 @ X15 @ X17) @ X16))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('221', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_A)
% 9.64/9.82          | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['219', '220'])).
% 9.64/9.82  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('223', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ X0)
% 9.64/9.82          | (v2_struct_0 @ sk_A)
% 9.64/9.82          | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['221', '222'])).
% 9.64/9.82  thf('224', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['218', '223'])).
% 9.64/9.82  thf('225', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 9.64/9.82      inference('sup+', [status(thm)], ['120', '121'])).
% 9.64/9.82  thf('226', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_A))),
% 9.64/9.82      inference('demod', [status(thm)], ['224', '225'])).
% 9.64/9.82  thf('227', plain,
% 9.64/9.82      (((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('simplify', [status(thm)], ['226'])).
% 9.64/9.82  thf('228', plain, (~ (v2_struct_0 @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('229', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_A))),
% 9.64/9.82      inference('clc', [status(thm)], ['227', '228'])).
% 9.64/9.82  thf('230', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('231', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ sk_A)),
% 9.64/9.82      inference('clc', [status(thm)], ['229', '230'])).
% 9.64/9.82  thf('232', plain,
% 9.64/9.82      (((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)) = (u1_struct_0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['167', '194'])).
% 9.64/9.82  thf('233', plain,
% 9.64/9.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X20 @ X21)
% 9.64/9.82          | ~ (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 9.64/9.82          | (m1_pre_topc @ X20 @ X22)
% 9.64/9.82          | ~ (m1_pre_topc @ X22 @ X21)
% 9.64/9.82          | ~ (l1_pre_topc @ X21)
% 9.64/9.82          | ~ (v2_pre_topc @ X21))),
% 9.64/9.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 9.64/9.82  thf('234', plain,
% 9.64/9.82      (![X0 : $i, X1 : $i]:
% 9.64/9.82         (~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C))
% 9.64/9.82          | ~ (v2_pre_topc @ X1)
% 9.64/9.82          | ~ (l1_pre_topc @ X1)
% 9.64/9.82          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C) @ X1)
% 9.64/9.82          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | ~ (m1_pre_topc @ X0 @ X1))),
% 9.64/9.82      inference('sup-', [status(thm)], ['232', '233'])).
% 9.64/9.82  thf('235', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.82          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82          | ~ (v2_pre_topc @ sk_A)
% 9.64/9.82          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('sup-', [status(thm)], ['231', '234'])).
% 9.64/9.82  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('238', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ sk_A)
% 9.64/9.82          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C)))),
% 9.64/9.82      inference('demod', [status(thm)], ['235', '236', '237'])).
% 9.64/9.82  thf('239', plain,
% 9.64/9.82      ((~ (r1_tarski @ 
% 9.64/9.82           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 9.64/9.82           (u1_struct_0 @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['217', '238'])).
% 9.64/9.82  thf('240', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A)
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('sup-', [status(thm)], ['200', '239'])).
% 9.64/9.82  thf('241', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['240'])).
% 9.64/9.82  thf('242', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['7', '241'])).
% 9.64/9.82  thf('243', plain,
% 9.64/9.82      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 9.64/9.82           (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['242'])).
% 9.64/9.82  thf('244', plain,
% 9.64/9.82      (((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 9.64/9.82         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 9.64/9.82      inference('clc', [status(thm)], ['64', '65'])).
% 9.64/9.82  thf(t59_pre_topc, axiom,
% 9.64/9.82    (![A:$i]:
% 9.64/9.82     ( ( l1_pre_topc @ A ) =>
% 9.64/9.82       ( ![B:$i]:
% 9.64/9.82         ( ( m1_pre_topc @
% 9.64/9.82             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 9.64/9.82           ( m1_pre_topc @ B @ A ) ) ) ))).
% 9.64/9.82  thf('245', plain,
% 9.64/9.82      (![X7 : $i, X8 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X7 @ 
% 9.64/9.82             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 9.64/9.82          | (m1_pre_topc @ X7 @ X8)
% 9.64/9.82          | ~ (l1_pre_topc @ X8))),
% 9.64/9.82      inference('cnf', [status(esa)], [t59_pre_topc])).
% 9.64/9.82  thf('246', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82          | (m1_pre_topc @ X0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['244', '245'])).
% 9.64/9.82  thf('247', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('248', plain,
% 9.64/9.82      (![X0 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C))
% 9.64/9.82          | (m1_pre_topc @ X0 @ sk_C))),
% 9.64/9.82      inference('demod', [status(thm)], ['246', '247'])).
% 9.64/9.82  thf('249', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['243', '248'])).
% 9.64/9.82  thf('250', plain,
% 9.64/9.82      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('251', plain,
% 9.64/9.82      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('sup-', [status(thm)], ['249', '250'])).
% 9.64/9.82  thf('252', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | ~ (v2_struct_0 @ (k1_tsep_1 @ X16 @ X15 @ X17)))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('253', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 9.64/9.82      inference('sup-', [status(thm)], ['251', '252'])).
% 9.64/9.82  thf('254', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('255', plain, ((l1_pre_topc @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('256', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('257', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('demod', [status(thm)], ['253', '254', '255', '256'])).
% 9.64/9.82  thf('258', plain,
% 9.64/9.82      (((v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['257'])).
% 9.64/9.82  thf('259', plain,
% 9.64/9.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.64/9.82         (~ (m1_pre_topc @ X15 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X15)
% 9.64/9.82          | ~ (l1_pre_topc @ X16)
% 9.64/9.82          | (v2_struct_0 @ X16)
% 9.64/9.82          | (v2_struct_0 @ X17)
% 9.64/9.82          | ~ (m1_pre_topc @ X17 @ X16)
% 9.64/9.82          | ~ (v2_struct_0 @ (k1_tsep_1 @ X16 @ X15 @ X17)))),
% 9.64/9.82      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 9.64/9.82  thf('260', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | ~ (l1_pre_topc @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | ~ (m1_pre_topc @ sk_B @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['258', '259'])).
% 9.64/9.82  thf('261', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('262', plain, ((l1_pre_topc @ sk_C)),
% 9.64/9.82      inference('demod', [status(thm)], ['14', '15'])).
% 9.64/9.82  thf('263', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('264', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_D)
% 9.64/9.82        | (v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 9.64/9.82  thf('265', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_C)
% 9.64/9.82        | (v2_struct_0 @ sk_B)
% 9.64/9.82        | (v2_struct_0 @ sk_A)
% 9.64/9.82        | (v2_struct_0 @ sk_D))),
% 9.64/9.82      inference('simplify', [status(thm)], ['264'])).
% 9.64/9.82  thf('266', plain, (~ (v2_struct_0 @ sk_A)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('267', plain,
% 9.64/9.82      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 9.64/9.82      inference('sup-', [status(thm)], ['265', '266'])).
% 9.64/9.82  thf('268', plain, (~ (v2_struct_0 @ sk_D)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('269', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 9.64/9.82      inference('clc', [status(thm)], ['267', '268'])).
% 9.64/9.82  thf('270', plain, (~ (v2_struct_0 @ sk_C)),
% 9.64/9.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.82  thf('271', plain, ((v2_struct_0 @ sk_B)),
% 9.64/9.82      inference('clc', [status(thm)], ['269', '270'])).
% 9.64/9.82  thf('272', plain, ($false), inference('demod', [status(thm)], ['0', '271'])).
% 9.64/9.82  
% 9.64/9.82  % SZS output end Refutation
% 9.64/9.82  
% 9.64/9.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
