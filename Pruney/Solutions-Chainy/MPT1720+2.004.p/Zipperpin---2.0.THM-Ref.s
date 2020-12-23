%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WEaEIiPIY0

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:28 EST 2020

% Result     : Theorem 32.04s
% Output     : Refutation 32.04s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 330 expanded)
%              Number of leaves         :   23 ( 100 expanded)
%              Depth                    :   26
%              Number of atoms          : 1777 (6449 expanded)
%              Number of equality atoms :   31 (  35 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( X6
       != ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
      | ( ( u1_struct_0 @ X6 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X5 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X5 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) @ X5 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 ) ) ),
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

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','24'])).

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

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( r1_tarski @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( k1_tsep_1 @ X15 @ X14 @ X14 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(t23_tsep_1,axiom,(
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
             => ( ( m1_pre_topc @ B @ C )
              <=> ( ( k1_tsep_1 @ A @ B @ C )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( ( k1_tsep_1 @ X12 @ X11 @ X13 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( m1_pre_topc @ X11 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tsep_1 @ X1 @ X0 @ sk_C )
       != ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['55','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('90',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X5 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) @ X5 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X5 @ X4 @ X7 ) )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('91',plain,
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
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
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
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('100',plain,
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
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ( m1_pre_topc @ X16 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WEaEIiPIY0
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 32.04/32.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.04/32.25  % Solved by: fo/fo7.sh
% 32.04/32.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.04/32.25  % done 13714 iterations in 31.787s
% 32.04/32.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.04/32.25  % SZS output start Refutation
% 32.04/32.25  thf(sk_A_type, type, sk_A: $i).
% 32.04/32.25  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 32.04/32.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 32.04/32.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 32.04/32.25  thf(sk_D_type, type, sk_D: $i).
% 32.04/32.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 32.04/32.25  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 32.04/32.25  thf(sk_B_type, type, sk_B: $i).
% 32.04/32.25  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 32.04/32.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 32.04/32.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 32.04/32.25  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 32.04/32.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 32.04/32.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.04/32.25  thf(sk_C_type, type, sk_C: $i).
% 32.04/32.25  thf(t29_tmap_1, conjecture,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.04/32.25       ( ![B:$i]:
% 32.04/32.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 32.04/32.25           ( ![C:$i]:
% 32.04/32.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 32.04/32.25               ( ![D:$i]:
% 32.04/32.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 32.04/32.25                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 32.04/32.25                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 32.04/32.25  thf(zf_stmt_0, negated_conjecture,
% 32.04/32.25    (~( ![A:$i]:
% 32.04/32.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 32.04/32.25            ( l1_pre_topc @ A ) ) =>
% 32.04/32.25          ( ![B:$i]:
% 32.04/32.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 32.04/32.25              ( ![C:$i]:
% 32.04/32.25                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 32.04/32.25                  ( ![D:$i]:
% 32.04/32.25                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 32.04/32.25                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 32.04/32.25                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 32.04/32.25    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 32.04/32.25  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf(dt_k1_tsep_1, axiom,
% 32.04/32.25    (![A:$i,B:$i,C:$i]:
% 32.04/32.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 32.04/32.25         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 32.04/32.25         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 32.04/32.25       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 32.04/32.25         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 32.04/32.25         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 32.04/32.25  thf('3', plain,
% 32.04/32.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X8 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X8)
% 32.04/32.25          | ~ (l1_pre_topc @ X9)
% 32.04/32.25          | (v2_struct_0 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X10)
% 32.04/32.25          | ~ (m1_pre_topc @ X10 @ X9)
% 32.04/32.25          | (m1_pre_topc @ (k1_tsep_1 @ X9 @ X8 @ X10) @ X9))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 32.04/32.25  thf('4', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_A)
% 32.04/32.25          | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('sup-', [status(thm)], ['2', '3'])).
% 32.04/32.25  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('6', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('demod', [status(thm)], ['4', '5'])).
% 32.04/32.25  thf('7', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 32.04/32.25      inference('sup-', [status(thm)], ['1', '6'])).
% 32.04/32.25  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('10', plain,
% 32.04/32.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X8 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X8)
% 32.04/32.25          | ~ (l1_pre_topc @ X9)
% 32.04/32.25          | (v2_struct_0 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X10)
% 32.04/32.25          | ~ (m1_pre_topc @ X10 @ X9)
% 32.04/32.25          | (v1_pre_topc @ (k1_tsep_1 @ X9 @ X8 @ X10)))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 32.04/32.25  thf('11', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | ~ (l1_pre_topc @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('sup-', [status(thm)], ['9', '10'])).
% 32.04/32.25  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf(dt_m1_pre_topc, axiom,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( l1_pre_topc @ A ) =>
% 32.04/32.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 32.04/32.25  thf('13', plain,
% 32.04/32.25      (![X2 : $i, X3 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 32.04/32.25  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['12', '13'])).
% 32.04/32.25  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 32.04/32.25      inference('demod', [status(thm)], ['14', '15'])).
% 32.04/32.25  thf('17', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('demod', [status(thm)], ['11', '16'])).
% 32.04/32.25  thf('18', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)))),
% 32.04/32.25      inference('sup-', [status(thm)], ['8', '17'])).
% 32.04/32.25  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('21', plain,
% 32.04/32.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X8 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X8)
% 32.04/32.25          | ~ (l1_pre_topc @ X9)
% 32.04/32.25          | (v2_struct_0 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X10)
% 32.04/32.25          | ~ (m1_pre_topc @ X10 @ X9)
% 32.04/32.25          | (m1_pre_topc @ (k1_tsep_1 @ X9 @ X8 @ X10) @ X9))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 32.04/32.25  thf('22', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | ~ (l1_pre_topc @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('sup-', [status(thm)], ['20', '21'])).
% 32.04/32.25  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 32.04/32.25      inference('demod', [status(thm)], ['14', '15'])).
% 32.04/32.25  thf('24', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('demod', [status(thm)], ['22', '23'])).
% 32.04/32.25  thf('25', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['19', '24'])).
% 32.04/32.25  thf(d2_tsep_1, axiom,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 32.04/32.25       ( ![B:$i]:
% 32.04/32.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 32.04/32.25           ( ![C:$i]:
% 32.04/32.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 32.04/32.25               ( ![D:$i]:
% 32.04/32.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 32.04/32.25                     ( m1_pre_topc @ D @ A ) ) =>
% 32.04/32.25                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 32.04/32.25                     ( ( u1_struct_0 @ D ) =
% 32.04/32.25                       ( k2_xboole_0 @
% 32.04/32.25                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 32.04/32.25  thf('26', plain,
% 32.04/32.25      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 32.04/32.25         ((v2_struct_0 @ X4)
% 32.04/32.25          | ~ (m1_pre_topc @ X4 @ X5)
% 32.04/32.25          | (v2_struct_0 @ X6)
% 32.04/32.25          | ~ (v1_pre_topc @ X6)
% 32.04/32.25          | ~ (m1_pre_topc @ X6 @ X5)
% 32.04/32.25          | ((X6) != (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25          | ((u1_struct_0 @ X6)
% 32.04/32.25              = (k2_xboole_0 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))
% 32.04/32.25          | ~ (m1_pre_topc @ X7 @ X5)
% 32.04/32.25          | (v2_struct_0 @ X7)
% 32.04/32.25          | ~ (l1_pre_topc @ X5)
% 32.04/32.25          | (v2_struct_0 @ X5))),
% 32.04/32.25      inference('cnf', [status(esa)], [d2_tsep_1])).
% 32.04/32.25  thf('27', plain,
% 32.04/32.25      (![X4 : $i, X5 : $i, X7 : $i]:
% 32.04/32.25         ((v2_struct_0 @ X5)
% 32.04/32.25          | ~ (l1_pre_topc @ X5)
% 32.04/32.25          | (v2_struct_0 @ X7)
% 32.04/32.25          | ~ (m1_pre_topc @ X7 @ X5)
% 32.04/32.25          | ((u1_struct_0 @ (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25              = (k2_xboole_0 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ X5 @ X4 @ X7) @ X5)
% 32.04/32.25          | ~ (v1_pre_topc @ (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25          | (v2_struct_0 @ (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25          | ~ (m1_pre_topc @ X4 @ X5)
% 32.04/32.25          | (v2_struct_0 @ X4))),
% 32.04/32.25      inference('simplify', [status(thm)], ['26'])).
% 32.04/32.25  thf('28', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['25', '27'])).
% 32.04/32.25  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 32.04/32.25      inference('demod', [status(thm)], ['14', '15'])).
% 32.04/32.25  thf('32', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 32.04/32.25  thf('33', plain,
% 32.04/32.25      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['32'])).
% 32.04/32.25  thf('34', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 32.04/32.25      inference('sup-', [status(thm)], ['18', '33'])).
% 32.04/32.25  thf('35', plain,
% 32.04/32.25      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['34'])).
% 32.04/32.25  thf('36', plain,
% 32.04/32.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X8 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X8)
% 32.04/32.25          | ~ (l1_pre_topc @ X9)
% 32.04/32.25          | (v2_struct_0 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X10)
% 32.04/32.25          | ~ (m1_pre_topc @ X10 @ X9)
% 32.04/32.25          | ~ (v2_struct_0 @ (k1_tsep_1 @ X9 @ X8 @ X10)))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 32.04/32.25  thf('37', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_B @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['35', '36'])).
% 32.04/32.25  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 32.04/32.25      inference('demod', [status(thm)], ['14', '15'])).
% 32.04/32.25  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('41', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 32.04/32.25  thf('42', plain,
% 32.04/32.25      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 32.04/32.25          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['41'])).
% 32.04/32.25  thf('43', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['19', '24'])).
% 32.04/32.25  thf('44', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['19', '24'])).
% 32.04/32.25  thf(t4_tsep_1, axiom,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.04/32.25       ( ![B:$i]:
% 32.04/32.25         ( ( m1_pre_topc @ B @ A ) =>
% 32.04/32.25           ( ![C:$i]:
% 32.04/32.25             ( ( m1_pre_topc @ C @ A ) =>
% 32.04/32.25               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 32.04/32.25                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 32.04/32.25  thf('45', plain,
% 32.04/32.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X16 @ X17)
% 32.04/32.25          | ~ (m1_pre_topc @ X16 @ X18)
% 32.04/32.25          | (r1_tarski @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18))
% 32.04/32.25          | ~ (m1_pre_topc @ X18 @ X17)
% 32.04/32.25          | ~ (l1_pre_topc @ X17)
% 32.04/32.25          | ~ (v2_pre_topc @ X17))),
% 32.04/32.25      inference('cnf', [status(esa)], [t4_tsep_1])).
% 32.04/32.25  thf('46', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v2_struct_0 @ sk_D)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B)
% 32.04/32.25          | ~ (v2_pre_topc @ sk_C)
% 32.04/32.25          | ~ (l1_pre_topc @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 32.04/32.25             (u1_struct_0 @ X0))
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ X0))),
% 32.04/32.25      inference('sup-', [status(thm)], ['44', '45'])).
% 32.04/32.25  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf(cc1_pre_topc, axiom,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.04/32.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 32.04/32.25  thf('48', plain,
% 32.04/32.25      (![X0 : $i, X1 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X0 @ X1)
% 32.04/32.25          | (v2_pre_topc @ X0)
% 32.04/32.25          | ~ (l1_pre_topc @ X1)
% 32.04/32.25          | ~ (v2_pre_topc @ X1))),
% 32.04/32.25      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 32.04/32.25  thf('49', plain,
% 32.04/32.25      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['47', '48'])).
% 32.04/32.25  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('52', plain, ((v2_pre_topc @ sk_C)),
% 32.04/32.25      inference('demod', [status(thm)], ['49', '50', '51'])).
% 32.04/32.25  thf('53', plain, ((l1_pre_topc @ sk_C)),
% 32.04/32.25      inference('demod', [status(thm)], ['14', '15'])).
% 32.04/32.25  thf('54', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v2_struct_0 @ sk_D)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 32.04/32.25             (u1_struct_0 @ X0))
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ X0))),
% 32.04/32.25      inference('demod', [status(thm)], ['46', '52', '53'])).
% 32.04/32.25  thf('55', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 32.04/32.25           (u1_struct_0 @ sk_C))
% 32.04/32.25        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('sup-', [status(thm)], ['43', '54'])).
% 32.04/32.25  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf(t25_tmap_1, axiom,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.04/32.25       ( ![B:$i]:
% 32.04/32.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 32.04/32.25           ( ( k1_tsep_1 @ A @ B @ B ) =
% 32.04/32.25             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 32.04/32.25  thf('57', plain,
% 32.04/32.25      (![X14 : $i, X15 : $i]:
% 32.04/32.25         ((v2_struct_0 @ X14)
% 32.04/32.25          | ~ (m1_pre_topc @ X14 @ X15)
% 32.04/32.25          | ((k1_tsep_1 @ X15 @ X14 @ X14)
% 32.04/32.25              = (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 32.04/32.25          | ~ (l1_pre_topc @ X15)
% 32.04/32.25          | ~ (v2_pre_topc @ X15)
% 32.04/32.25          | (v2_struct_0 @ X15))),
% 32.04/32.25      inference('cnf', [status(esa)], [t25_tmap_1])).
% 32.04/32.25  thf('58', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_A)
% 32.04/32.25        | ~ (v2_pre_topc @ sk_A)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 32.04/32.25            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['56', '57'])).
% 32.04/32.25  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('61', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_A)
% 32.04/32.25        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 32.04/32.25            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('demod', [status(thm)], ['58', '59', '60'])).
% 32.04/32.25  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('63', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_C)
% 32.04/32.25        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 32.04/32.25            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 32.04/32.25      inference('clc', [status(thm)], ['61', '62'])).
% 32.04/32.25  thf('64', plain, (~ (v2_struct_0 @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('65', plain,
% 32.04/32.25      (((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 32.04/32.25         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 32.04/32.25      inference('clc', [status(thm)], ['63', '64'])).
% 32.04/32.25  thf(t23_tsep_1, axiom,
% 32.04/32.25    (![A:$i]:
% 32.04/32.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 32.04/32.25       ( ![B:$i]:
% 32.04/32.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 32.04/32.25           ( ![C:$i]:
% 32.04/32.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 32.04/32.25               ( ( m1_pre_topc @ B @ C ) <=>
% 32.04/32.25                 ( ( k1_tsep_1 @ A @ B @ C ) =
% 32.04/32.25                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 32.04/32.25  thf('66', plain,
% 32.04/32.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.04/32.25         ((v2_struct_0 @ X11)
% 32.04/32.25          | ~ (m1_pre_topc @ X11 @ X12)
% 32.04/32.25          | ((k1_tsep_1 @ X12 @ X11 @ X13)
% 32.04/32.25              != (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 32.04/32.25          | (m1_pre_topc @ X11 @ X13)
% 32.04/32.25          | ~ (m1_pre_topc @ X13 @ X12)
% 32.04/32.25          | (v2_struct_0 @ X13)
% 32.04/32.25          | ~ (l1_pre_topc @ X12)
% 32.04/32.25          | ~ (v2_pre_topc @ X12)
% 32.04/32.25          | (v2_struct_0 @ X12))),
% 32.04/32.25      inference('cnf', [status(esa)], [t23_tsep_1])).
% 32.04/32.25  thf('67', plain,
% 32.04/32.25      (![X0 : $i, X1 : $i]:
% 32.04/32.25         (((k1_tsep_1 @ X1 @ X0 @ sk_C) != (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 32.04/32.25          | (v2_struct_0 @ X1)
% 32.04/32.25          | ~ (v2_pre_topc @ X1)
% 32.04/32.25          | ~ (l1_pre_topc @ X1)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ sk_C @ X1)
% 32.04/32.25          | (m1_pre_topc @ X0 @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ X1)
% 32.04/32.25          | (v2_struct_0 @ X0))),
% 32.04/32.25      inference('sup-', [status(thm)], ['65', '66'])).
% 32.04/32.25  thf('68', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_C)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 32.04/32.25        | (m1_pre_topc @ sk_C @ sk_C)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25        | ~ (v2_pre_topc @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_A))),
% 32.04/32.25      inference('eq_res', [status(thm)], ['67'])).
% 32.04/32.25  thf('69', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_A)
% 32.04/32.25        | ~ (v2_pre_topc @ sk_A)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25        | (m1_pre_topc @ sk_C @ sk_C)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('simplify', [status(thm)], ['68'])).
% 32.04/32.25  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('73', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_A)
% 32.04/32.25        | (m1_pre_topc @ sk_C @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 32.04/32.25  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('75', plain, (((v2_struct_0 @ sk_C) | (m1_pre_topc @ sk_C @ sk_C))),
% 32.04/32.25      inference('clc', [status(thm)], ['73', '74'])).
% 32.04/32.25  thf('76', plain, (~ (v2_struct_0 @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 32.04/32.25      inference('clc', [status(thm)], ['75', '76'])).
% 32.04/32.25  thf('78', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 32.04/32.25           (u1_struct_0 @ sk_C))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('demod', [status(thm)], ['55', '77'])).
% 32.04/32.25  thf('79', plain,
% 32.04/32.25      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 32.04/32.25         (u1_struct_0 @ sk_C))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['78'])).
% 32.04/32.25  thf('80', plain,
% 32.04/32.25      (((r1_tarski @ 
% 32.04/32.25         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 32.04/32.25         (u1_struct_0 @ sk_C))
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('sup+', [status(thm)], ['42', '79'])).
% 32.04/32.25  thf('81', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (r1_tarski @ 
% 32.04/32.25           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 32.04/32.25           (u1_struct_0 @ sk_C)))),
% 32.04/32.25      inference('simplify', [status(thm)], ['80'])).
% 32.04/32.25  thf('82', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('83', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('84', plain,
% 32.04/32.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X8 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X8)
% 32.04/32.25          | ~ (l1_pre_topc @ X9)
% 32.04/32.25          | (v2_struct_0 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X10)
% 32.04/32.25          | ~ (m1_pre_topc @ X10 @ X9)
% 32.04/32.25          | (v1_pre_topc @ (k1_tsep_1 @ X9 @ X8 @ X10)))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 32.04/32.25  thf('85', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_A)
% 32.04/32.25          | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('sup-', [status(thm)], ['83', '84'])).
% 32.04/32.25  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('87', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('demod', [status(thm)], ['85', '86'])).
% 32.04/32.25  thf('88', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 32.04/32.25      inference('sup-', [status(thm)], ['82', '87'])).
% 32.04/32.25  thf('89', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 32.04/32.25      inference('sup-', [status(thm)], ['1', '6'])).
% 32.04/32.25  thf('90', plain,
% 32.04/32.25      (![X4 : $i, X5 : $i, X7 : $i]:
% 32.04/32.25         ((v2_struct_0 @ X5)
% 32.04/32.25          | ~ (l1_pre_topc @ X5)
% 32.04/32.25          | (v2_struct_0 @ X7)
% 32.04/32.25          | ~ (m1_pre_topc @ X7 @ X5)
% 32.04/32.25          | ((u1_struct_0 @ (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25              = (k2_xboole_0 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X7)))
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ X5 @ X4 @ X7) @ X5)
% 32.04/32.25          | ~ (v1_pre_topc @ (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25          | (v2_struct_0 @ (k1_tsep_1 @ X5 @ X4 @ X7))
% 32.04/32.25          | ~ (m1_pre_topc @ X4 @ X5)
% 32.04/32.25          | (v2_struct_0 @ X4))),
% 32.04/32.25      inference('simplify', [status(thm)], ['26'])).
% 32.04/32.25  thf('91', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_A))),
% 32.04/32.25      inference('sup-', [status(thm)], ['89', '90'])).
% 32.04/32.25  thf('92', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('93', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('95', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A))),
% 32.04/32.25      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 32.04/32.25  thf('96', plain,
% 32.04/32.25      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['95'])).
% 32.04/32.25  thf('97', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 32.04/32.25      inference('sup-', [status(thm)], ['88', '96'])).
% 32.04/32.25  thf('98', plain,
% 32.04/32.25      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['97'])).
% 32.04/32.25  thf('99', plain,
% 32.04/32.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X8 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X8)
% 32.04/32.25          | ~ (l1_pre_topc @ X9)
% 32.04/32.25          | (v2_struct_0 @ X9)
% 32.04/32.25          | (v2_struct_0 @ X10)
% 32.04/32.25          | ~ (m1_pre_topc @ X10 @ X9)
% 32.04/32.25          | ~ (v2_struct_0 @ (k1_tsep_1 @ X9 @ X8 @ X10)))),
% 32.04/32.25      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 32.04/32.25  thf('100', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 32.04/32.25      inference('sup-', [status(thm)], ['98', '99'])).
% 32.04/32.25  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('103', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('104', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 32.04/32.25  thf('105', plain,
% 32.04/32.25      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 32.04/32.25          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['104'])).
% 32.04/32.25  thf('106', plain,
% 32.04/32.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 32.04/32.25         (~ (m1_pre_topc @ X16 @ X17)
% 32.04/32.25          | ~ (r1_tarski @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18))
% 32.04/32.25          | (m1_pre_topc @ X16 @ X18)
% 32.04/32.25          | ~ (m1_pre_topc @ X18 @ X17)
% 32.04/32.25          | ~ (l1_pre_topc @ X17)
% 32.04/32.25          | ~ (v2_pre_topc @ X17))),
% 32.04/32.25      inference('cnf', [status(esa)], [t4_tsep_1])).
% 32.04/32.25  thf('107', plain,
% 32.04/32.25      (![X0 : $i, X1 : $i]:
% 32.04/32.25         (~ (r1_tarski @ 
% 32.04/32.25             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 32.04/32.25             (u1_struct_0 @ X0))
% 32.04/32.25          | (v2_struct_0 @ sk_D)
% 32.04/32.25          | (v2_struct_0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ sk_B)
% 32.04/32.25          | ~ (v2_pre_topc @ X1)
% 32.04/32.25          | ~ (l1_pre_topc @ X1)
% 32.04/32.25          | ~ (m1_pre_topc @ X0 @ X1)
% 32.04/32.25          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X1))),
% 32.04/32.25      inference('sup-', [status(thm)], ['105', '106'])).
% 32.04/32.25  thf('108', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v2_struct_0 @ sk_D)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_B)
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 32.04/32.25          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ sk_C @ X0)
% 32.04/32.25          | ~ (l1_pre_topc @ X0)
% 32.04/32.25          | ~ (v2_pre_topc @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_B)
% 32.04/32.25          | (v2_struct_0 @ sk_A)
% 32.04/32.25          | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('sup-', [status(thm)], ['81', '107'])).
% 32.04/32.25  thf('109', plain,
% 32.04/32.25      (![X0 : $i]:
% 32.04/32.25         ((v2_struct_0 @ sk_A)
% 32.04/32.25          | ~ (v2_pre_topc @ X0)
% 32.04/32.25          | ~ (l1_pre_topc @ X0)
% 32.04/32.25          | ~ (m1_pre_topc @ sk_C @ X0)
% 32.04/32.25          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 32.04/32.25          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 32.04/32.25          | (v2_struct_0 @ sk_B)
% 32.04/32.25          | (v2_struct_0 @ sk_C)
% 32.04/32.25          | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['108'])).
% 32.04/32.25  thf('110', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 32.04/32.25        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 32.04/32.25        | ~ (l1_pre_topc @ sk_A)
% 32.04/32.25        | ~ (v2_pre_topc @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_A))),
% 32.04/32.25      inference('sup-', [status(thm)], ['7', '109'])).
% 32.04/32.25  thf('111', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('114', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_A))),
% 32.04/32.25      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 32.04/32.25  thf('115', plain,
% 32.04/32.25      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_C)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('simplify', [status(thm)], ['114'])).
% 32.04/32.25  thf('116', plain,
% 32.04/32.25      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('117', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_D)
% 32.04/32.25        | (v2_struct_0 @ sk_A)
% 32.04/32.25        | (v2_struct_0 @ sk_B)
% 32.04/32.25        | (v2_struct_0 @ sk_C))),
% 32.04/32.25      inference('sup-', [status(thm)], ['115', '116'])).
% 32.04/32.25  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('119', plain,
% 32.04/32.25      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 32.04/32.25      inference('sup-', [status(thm)], ['117', '118'])).
% 32.04/32.25  thf('120', plain, (~ (v2_struct_0 @ sk_C)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('121', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 32.04/32.25      inference('clc', [status(thm)], ['119', '120'])).
% 32.04/32.25  thf('122', plain, (~ (v2_struct_0 @ sk_D)),
% 32.04/32.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.04/32.25  thf('123', plain, ((v2_struct_0 @ sk_B)),
% 32.04/32.25      inference('clc', [status(thm)], ['121', '122'])).
% 32.04/32.25  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 32.04/32.25  
% 32.04/32.25  % SZS output end Refutation
% 32.04/32.25  
% 32.04/32.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
