%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnS2IreW1s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:30 EST 2020

% Result     : Theorem 27.57s
% Output     : Refutation 27.57s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 267 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :   32
%              Number of atoms          : 1712 (5492 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X7 @ X6 @ X8 ) @ X7 ) ) ),
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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X7 @ X6 @ X8 ) ) ) ),
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
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( X4
       != ( k1_tsep_1 @ X3 @ X2 @ X5 ) )
      | ( ( u1_struct_0 @ X4 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_pre_topc @ X5 @ X3 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X3 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X3 @ X2 @ X5 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X3 @ X2 @ X5 ) @ X3 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X3 @ X2 @ X5 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X3 @ X2 @ X5 ) )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
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
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
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
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('29',plain,
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
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['34','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_tmap_1,axiom,(
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
                     => ( ( ( m1_pre_topc @ B @ C )
                          & ( m1_pre_topc @ D @ E ) )
                       => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ ( k1_tsep_1 @ A @ C @ E ) ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X16 ) @ ( k1_tsep_1 @ X15 @ X17 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X15 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t27_tmap_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X2 ) @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X2 ) @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k1_tsep_1 @ X13 @ X12 @ X12 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

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

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( k1_tsep_1 @ X10 @ X9 @ X11 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ( m1_pre_topc @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tsep_1 @ X1 @ X0 @ sk_B )
       != ( k1_tsep_1 @ sk_A @ sk_B @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('88',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,
    ( ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['47','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ( m1_pre_topc @ X19 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnS2IreW1s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 27.57/27.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 27.57/27.76  % Solved by: fo/fo7.sh
% 27.57/27.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.57/27.76  % done 9981 iterations in 27.305s
% 27.57/27.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 27.57/27.76  % SZS output start Refutation
% 27.57/27.76  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 27.57/27.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 27.57/27.76  thf(sk_A_type, type, sk_A: $i).
% 27.57/27.76  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 27.57/27.76  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 27.57/27.76  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 27.57/27.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.57/27.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 27.57/27.76  thf(sk_D_type, type, sk_D: $i).
% 27.57/27.76  thf(sk_B_type, type, sk_B: $i).
% 27.57/27.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 27.57/27.76  thf(sk_C_type, type, sk_C: $i).
% 27.57/27.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 27.57/27.76  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 27.57/27.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 27.57/27.76  thf(t29_tmap_1, conjecture,
% 27.57/27.76    (![A:$i]:
% 27.57/27.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.57/27.76       ( ![B:$i]:
% 27.57/27.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 27.57/27.76           ( ![C:$i]:
% 27.57/27.76             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 27.57/27.76               ( ![D:$i]:
% 27.57/27.76                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 27.57/27.76                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 27.57/27.76                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 27.57/27.76  thf(zf_stmt_0, negated_conjecture,
% 27.57/27.76    (~( ![A:$i]:
% 27.57/27.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 27.57/27.76            ( l1_pre_topc @ A ) ) =>
% 27.57/27.76          ( ![B:$i]:
% 27.57/27.76            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 27.57/27.76              ( ![C:$i]:
% 27.57/27.76                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 27.57/27.76                  ( ![D:$i]:
% 27.57/27.76                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 27.57/27.76                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 27.57/27.76                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 27.57/27.76    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 27.57/27.76  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 27.57/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.76  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 27.57/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.76  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.76  thf(dt_k1_tsep_1, axiom,
% 27.57/27.76    (![A:$i,B:$i,C:$i]:
% 27.57/27.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 27.57/27.76         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 27.57/27.76         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 27.57/27.76       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 27.57/27.76         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 27.57/27.76         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 27.57/27.76  thf('3', plain,
% 27.57/27.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.57/27.76         (~ (m1_pre_topc @ X6 @ X7)
% 27.57/27.76          | (v2_struct_0 @ X6)
% 27.57/27.76          | ~ (l1_pre_topc @ X7)
% 27.57/27.77          | (v2_struct_0 @ X7)
% 27.57/27.77          | (v2_struct_0 @ X8)
% 27.57/27.77          | ~ (m1_pre_topc @ X8 @ X7)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X8) @ X7))),
% 27.57/27.77      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 27.57/27.77  thf('4', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('sup-', [status(thm)], ['2', '3'])).
% 27.57/27.77  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('6', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['4', '5'])).
% 27.57/27.77  thf('7', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['1', '6'])).
% 27.57/27.77  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('10', plain,
% 27.57/27.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.57/27.77         (~ (m1_pre_topc @ X6 @ X7)
% 27.57/27.77          | (v2_struct_0 @ X6)
% 27.57/27.77          | ~ (l1_pre_topc @ X7)
% 27.57/27.77          | (v2_struct_0 @ X7)
% 27.57/27.77          | (v2_struct_0 @ X8)
% 27.57/27.77          | ~ (m1_pre_topc @ X8 @ X7)
% 27.57/27.77          | (v1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X8)))),
% 27.57/27.77      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 27.57/27.77  thf('11', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('sup-', [status(thm)], ['9', '10'])).
% 27.57/27.77  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('13', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['11', '12'])).
% 27.57/27.77  thf('14', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 27.57/27.77      inference('sup-', [status(thm)], ['8', '13'])).
% 27.57/27.77  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('16', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['4', '5'])).
% 27.57/27.77  thf('17', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['15', '16'])).
% 27.57/27.77  thf(d2_tsep_1, axiom,
% 27.57/27.77    (![A:$i]:
% 27.57/27.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 27.57/27.77       ( ![B:$i]:
% 27.57/27.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 27.57/27.77           ( ![C:$i]:
% 27.57/27.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 27.57/27.77               ( ![D:$i]:
% 27.57/27.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 27.57/27.77                     ( m1_pre_topc @ D @ A ) ) =>
% 27.57/27.77                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 27.57/27.77                     ( ( u1_struct_0 @ D ) =
% 27.57/27.77                       ( k2_xboole_0 @
% 27.57/27.77                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 27.57/27.77  thf('18', plain,
% 27.57/27.77      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.57/27.77         ((v2_struct_0 @ X2)
% 27.57/27.77          | ~ (m1_pre_topc @ X2 @ X3)
% 27.57/27.77          | (v2_struct_0 @ X4)
% 27.57/27.77          | ~ (v1_pre_topc @ X4)
% 27.57/27.77          | ~ (m1_pre_topc @ X4 @ X3)
% 27.57/27.77          | ((X4) != (k1_tsep_1 @ X3 @ X2 @ X5))
% 27.57/27.77          | ((u1_struct_0 @ X4)
% 27.57/27.77              = (k2_xboole_0 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X5)))
% 27.57/27.77          | ~ (m1_pre_topc @ X5 @ X3)
% 27.57/27.77          | (v2_struct_0 @ X5)
% 27.57/27.77          | ~ (l1_pre_topc @ X3)
% 27.57/27.77          | (v2_struct_0 @ X3))),
% 27.57/27.77      inference('cnf', [status(esa)], [d2_tsep_1])).
% 27.57/27.77  thf('19', plain,
% 27.57/27.77      (![X2 : $i, X3 : $i, X5 : $i]:
% 27.57/27.77         ((v2_struct_0 @ X3)
% 27.57/27.77          | ~ (l1_pre_topc @ X3)
% 27.57/27.77          | (v2_struct_0 @ X5)
% 27.57/27.77          | ~ (m1_pre_topc @ X5 @ X3)
% 27.57/27.77          | ((u1_struct_0 @ (k1_tsep_1 @ X3 @ X2 @ X5))
% 27.57/27.77              = (k2_xboole_0 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X5)))
% 27.57/27.77          | ~ (m1_pre_topc @ (k1_tsep_1 @ X3 @ X2 @ X5) @ X3)
% 27.57/27.77          | ~ (v1_pre_topc @ (k1_tsep_1 @ X3 @ X2 @ X5))
% 27.57/27.77          | (v2_struct_0 @ (k1_tsep_1 @ X3 @ X2 @ X5))
% 27.57/27.77          | ~ (m1_pre_topc @ X2 @ X3)
% 27.57/27.77          | (v2_struct_0 @ X2))),
% 27.57/27.77      inference('simplify', [status(thm)], ['18'])).
% 27.57/27.77  thf('20', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['17', '19'])).
% 27.57/27.77  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('24', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A))),
% 27.57/27.77      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 27.57/27.77  thf('25', plain,
% 27.57/27.77      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('simplify', [status(thm)], ['24'])).
% 27.57/27.77  thf('26', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 27.57/27.77      inference('sup-', [status(thm)], ['14', '25'])).
% 27.57/27.77  thf('27', plain,
% 27.57/27.77      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('simplify', [status(thm)], ['26'])).
% 27.57/27.77  thf('28', plain,
% 27.57/27.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 27.57/27.77         (~ (m1_pre_topc @ X6 @ X7)
% 27.57/27.77          | (v2_struct_0 @ X6)
% 27.57/27.77          | ~ (l1_pre_topc @ X7)
% 27.57/27.77          | (v2_struct_0 @ X7)
% 27.57/27.77          | (v2_struct_0 @ X8)
% 27.57/27.77          | ~ (m1_pre_topc @ X8 @ X7)
% 27.57/27.77          | ~ (v2_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X8)))),
% 27.57/27.77      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 27.57/27.77  thf('29', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['27', '28'])).
% 27.57/27.77  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('33', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 27.57/27.77  thf('34', plain,
% 27.57/27.77      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('simplify', [status(thm)], ['33'])).
% 27.57/27.77  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf(t4_tsep_1, axiom,
% 27.57/27.77    (![A:$i]:
% 27.57/27.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.57/27.77       ( ![B:$i]:
% 27.57/27.77         ( ( m1_pre_topc @ B @ A ) =>
% 27.57/27.77           ( ![C:$i]:
% 27.57/27.77             ( ( m1_pre_topc @ C @ A ) =>
% 27.57/27.77               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 27.57/27.77                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 27.57/27.77  thf('37', plain,
% 27.57/27.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 27.57/27.77         (~ (m1_pre_topc @ X19 @ X20)
% 27.57/27.77          | ~ (m1_pre_topc @ X19 @ X21)
% 27.57/27.77          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 27.57/27.77          | ~ (m1_pre_topc @ X21 @ X20)
% 27.57/27.77          | ~ (l1_pre_topc @ X20)
% 27.57/27.77          | ~ (v2_pre_topc @ X20))),
% 27.57/27.77      inference('cnf', [status(esa)], [t4_tsep_1])).
% 27.57/27.77  thf('38', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         (~ (v2_pre_topc @ sk_A)
% 27.57/27.77          | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 27.57/27.77          | ~ (m1_pre_topc @ sk_B @ X0))),
% 27.57/27.77      inference('sup-', [status(thm)], ['36', '37'])).
% 27.57/27.77  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('41', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 27.57/27.77          | ~ (m1_pre_topc @ sk_B @ X0))),
% 27.57/27.77      inference('demod', [status(thm)], ['38', '39', '40'])).
% 27.57/27.77  thf('42', plain,
% 27.57/27.77      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 27.57/27.77        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 27.57/27.77      inference('sup-', [status(thm)], ['35', '41'])).
% 27.57/27.77  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('44', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 27.57/27.77      inference('demod', [status(thm)], ['42', '43'])).
% 27.57/27.77  thf(t12_xboole_1, axiom,
% 27.57/27.77    (![A:$i,B:$i]:
% 27.57/27.77     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 27.57/27.77  thf('45', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i]:
% 27.57/27.77         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 27.57/27.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 27.57/27.77  thf('46', plain,
% 27.57/27.77      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 27.57/27.77         = (u1_struct_0 @ sk_C))),
% 27.57/27.77      inference('sup-', [status(thm)], ['44', '45'])).
% 27.57/27.77  thf('47', plain,
% 27.57/27.77      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77          = (u1_struct_0 @ sk_C))
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('demod', [status(thm)], ['34', '46'])).
% 27.57/27.77  thf('48', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['15', '16'])).
% 27.57/27.77  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('50', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('52', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf(t27_tmap_1, axiom,
% 27.57/27.77    (![A:$i]:
% 27.57/27.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.57/27.77       ( ![B:$i]:
% 27.57/27.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 27.57/27.77           ( ![C:$i]:
% 27.57/27.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 27.57/27.77               ( ![D:$i]:
% 27.57/27.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 27.57/27.77                   ( ![E:$i]:
% 27.57/27.77                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 27.57/27.77                       ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ E ) ) =>
% 27.57/27.77                         ( m1_pre_topc @
% 27.57/27.77                           ( k1_tsep_1 @ A @ B @ D ) @ 
% 27.57/27.77                           ( k1_tsep_1 @ A @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 27.57/27.77  thf('53', plain,
% 27.57/27.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 27.57/27.77         ((v2_struct_0 @ X14)
% 27.57/27.77          | ~ (m1_pre_topc @ X14 @ X15)
% 27.57/27.77          | (v2_struct_0 @ X16)
% 27.57/27.77          | ~ (m1_pre_topc @ X16 @ X15)
% 27.57/27.77          | ~ (m1_pre_topc @ X14 @ X17)
% 27.57/27.77          | ~ (m1_pre_topc @ X16 @ X18)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X16) @ 
% 27.57/27.77             (k1_tsep_1 @ X15 @ X17 @ X18))
% 27.57/27.77          | ~ (m1_pre_topc @ X18 @ X15)
% 27.57/27.77          | (v2_struct_0 @ X18)
% 27.57/27.77          | ~ (m1_pre_topc @ X17 @ X15)
% 27.57/27.77          | (v2_struct_0 @ X17)
% 27.57/27.77          | ~ (l1_pre_topc @ X15)
% 27.57/27.77          | ~ (v2_pre_topc @ X15)
% 27.57/27.77          | (v2_struct_0 @ X15))),
% 27.57/27.77      inference('cnf', [status(esa)], [t27_tmap_1])).
% 27.57/27.77  thf('54', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_A)
% 27.57/27.77          | ~ (v2_pre_topc @ sk_A)
% 27.57/27.77          | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X1)
% 27.57/27.77          | ~ (m1_pre_topc @ X1 @ sk_A)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X2) @ 
% 27.57/27.77             (k1_tsep_1 @ sk_A @ X0 @ X1))
% 27.57/27.77          | ~ (m1_pre_topc @ X2 @ X1)
% 27.57/27.77          | ~ (m1_pre_topc @ sk_B @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X2 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X2)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('sup-', [status(thm)], ['52', '53'])).
% 27.57/27.77  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('57', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X1)
% 27.57/27.77          | ~ (m1_pre_topc @ X1 @ sk_A)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X2) @ 
% 27.57/27.77             (k1_tsep_1 @ sk_A @ X0 @ X1))
% 27.57/27.77          | ~ (m1_pre_topc @ X2 @ X1)
% 27.57/27.77          | ~ (m1_pre_topc @ sk_B @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X2 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X2)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['54', '55', '56'])).
% 27.57/27.77  thf('58', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_B)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ X1)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 27.57/27.77             (k1_tsep_1 @ sk_A @ sk_B @ X1))
% 27.57/27.77          | ~ (m1_pre_topc @ X1 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X1)
% 27.57/27.77          | (v2_struct_0 @ sk_B)
% 27.57/27.77          | (v2_struct_0 @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['51', '57'])).
% 27.57/27.77  thf('59', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf(t25_tmap_1, axiom,
% 27.57/27.77    (![A:$i]:
% 27.57/27.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.57/27.77       ( ![B:$i]:
% 27.57/27.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 27.57/27.77           ( ( k1_tsep_1 @ A @ B @ B ) =
% 27.57/27.77             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 27.57/27.77  thf('60', plain,
% 27.57/27.77      (![X12 : $i, X13 : $i]:
% 27.57/27.77         ((v2_struct_0 @ X12)
% 27.57/27.77          | ~ (m1_pre_topc @ X12 @ X13)
% 27.57/27.77          | ((k1_tsep_1 @ X13 @ X12 @ X12)
% 27.57/27.77              = (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 27.57/27.77          | ~ (l1_pre_topc @ X13)
% 27.57/27.77          | ~ (v2_pre_topc @ X13)
% 27.57/27.77          | (v2_struct_0 @ X13))),
% 27.57/27.77      inference('cnf', [status(esa)], [t25_tmap_1])).
% 27.57/27.77  thf('61', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_A)
% 27.57/27.77        | ~ (v2_pre_topc @ sk_A)
% 27.57/27.77        | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 27.57/27.77            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('sup-', [status(thm)], ['59', '60'])).
% 27.57/27.77  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('64', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_A)
% 27.57/27.77        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 27.57/27.77            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['61', '62', '63'])).
% 27.57/27.77  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('66', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 27.57/27.77            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 27.57/27.77      inference('clc', [status(thm)], ['64', '65'])).
% 27.57/27.77  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('68', plain,
% 27.57/27.77      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 27.57/27.77         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 27.57/27.77      inference('clc', [status(thm)], ['66', '67'])).
% 27.57/27.77  thf(t23_tsep_1, axiom,
% 27.57/27.77    (![A:$i]:
% 27.57/27.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.57/27.77       ( ![B:$i]:
% 27.57/27.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 27.57/27.77           ( ![C:$i]:
% 27.57/27.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 27.57/27.77               ( ( m1_pre_topc @ B @ C ) <=>
% 27.57/27.77                 ( ( k1_tsep_1 @ A @ B @ C ) =
% 27.57/27.77                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 27.57/27.77  thf('69', plain,
% 27.57/27.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 27.57/27.77         ((v2_struct_0 @ X9)
% 27.57/27.77          | ~ (m1_pre_topc @ X9 @ X10)
% 27.57/27.77          | ((k1_tsep_1 @ X10 @ X9 @ X11)
% 27.57/27.77              != (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 27.57/27.77          | (m1_pre_topc @ X9 @ X11)
% 27.57/27.77          | ~ (m1_pre_topc @ X11 @ X10)
% 27.57/27.77          | (v2_struct_0 @ X11)
% 27.57/27.77          | ~ (l1_pre_topc @ X10)
% 27.57/27.77          | ~ (v2_pre_topc @ X10)
% 27.57/27.77          | (v2_struct_0 @ X10))),
% 27.57/27.77      inference('cnf', [status(esa)], [t23_tsep_1])).
% 27.57/27.77  thf('70', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i]:
% 27.57/27.77         (((k1_tsep_1 @ X1 @ X0 @ sk_B) != (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 27.57/27.77          | (v2_struct_0 @ X1)
% 27.57/27.77          | ~ (v2_pre_topc @ X1)
% 27.57/27.77          | ~ (l1_pre_topc @ X1)
% 27.57/27.77          | (v2_struct_0 @ sk_B)
% 27.57/27.77          | ~ (m1_pre_topc @ sk_B @ X1)
% 27.57/27.77          | (m1_pre_topc @ X0 @ sk_B)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ X1)
% 27.57/27.77          | (v2_struct_0 @ X0))),
% 27.57/27.77      inference('sup-', [status(thm)], ['68', '69'])).
% 27.57/27.77  thf('71', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 27.57/27.77        | (m1_pre_topc @ sk_B @ sk_B)
% 27.57/27.77        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77        | ~ (v2_pre_topc @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_A))),
% 27.57/27.77      inference('eq_res', [status(thm)], ['70'])).
% 27.57/27.77  thf('72', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_A)
% 27.57/27.77        | ~ (v2_pre_topc @ sk_A)
% 27.57/27.77        | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77        | (m1_pre_topc @ sk_B @ sk_B)
% 27.57/27.77        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('simplify', [status(thm)], ['71'])).
% 27.57/27.77  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('76', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_A)
% 27.57/27.77        | (m1_pre_topc @ sk_B @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 27.57/27.77  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('78', plain, (((v2_struct_0 @ sk_B) | (m1_pre_topc @ sk_B @ sk_B))),
% 27.57/27.77      inference('clc', [status(thm)], ['76', '77'])).
% 27.57/27.77  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('80', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 27.57/27.77      inference('clc', [status(thm)], ['78', '79'])).
% 27.57/27.77  thf('81', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_B)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ X1)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 27.57/27.77             (k1_tsep_1 @ sk_A @ sk_B @ X1))
% 27.57/27.77          | ~ (m1_pre_topc @ X1 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X1)
% 27.57/27.77          | (v2_struct_0 @ sk_B)
% 27.57/27.77          | (v2_struct_0 @ sk_A))),
% 27.57/27.77      inference('demod', [status(thm)], ['58', '80'])).
% 27.57/27.77  thf('82', plain,
% 27.57/27.77      (![X0 : $i, X1 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X1)
% 27.57/27.77          | ~ (m1_pre_topc @ X1 @ sk_A)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 27.57/27.77             (k1_tsep_1 @ sk_A @ sk_B @ X1))
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ X1)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('simplify', [status(thm)], ['81'])).
% 27.57/27.77  thf('83', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_B)
% 27.57/27.77          | (v2_struct_0 @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 27.57/27.77             (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77          | (v2_struct_0 @ sk_C)
% 27.57/27.77          | (v2_struct_0 @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['50', '82'])).
% 27.57/27.77  thf('84', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 27.57/27.77           (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('sup-', [status(thm)], ['49', '83'])).
% 27.57/27.77  thf('85', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('86', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 27.57/27.77           (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('demod', [status(thm)], ['84', '85'])).
% 27.57/27.77  thf('87', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 27.57/27.77      inference('sup-', [status(thm)], ['1', '6'])).
% 27.57/27.77  thf('88', plain,
% 27.57/27.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 27.57/27.77         (~ (m1_pre_topc @ X19 @ X20)
% 27.57/27.77          | ~ (m1_pre_topc @ X19 @ X21)
% 27.57/27.77          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 27.57/27.77          | ~ (m1_pre_topc @ X21 @ X20)
% 27.57/27.77          | ~ (l1_pre_topc @ X20)
% 27.57/27.77          | ~ (v2_pre_topc @ X20))),
% 27.57/27.77      inference('cnf', [status(esa)], [t4_tsep_1])).
% 27.57/27.77  thf('89', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_D)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B)
% 27.57/27.77          | ~ (v2_pre_topc @ sk_A)
% 27.57/27.77          | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77             (u1_struct_0 @ X0))
% 27.57/27.77          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0))),
% 27.57/27.77      inference('sup-', [status(thm)], ['87', '88'])).
% 27.57/27.77  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('92', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_D)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B)
% 27.57/27.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 27.57/27.77          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77             (u1_struct_0 @ X0))
% 27.57/27.77          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0))),
% 27.57/27.77      inference('demod', [status(thm)], ['89', '90', '91'])).
% 27.57/27.77  thf('93', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 27.57/27.77        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_D))),
% 27.57/27.77      inference('sup-', [status(thm)], ['86', '92'])).
% 27.57/27.77  thf('94', plain,
% 27.57/27.77      ((~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 27.57/27.77        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('simplify', [status(thm)], ['93'])).
% 27.57/27.77  thf('95', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 27.57/27.77      inference('sup-', [status(thm)], ['48', '94'])).
% 27.57/27.77  thf('96', plain,
% 27.57/27.77      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('simplify', [status(thm)], ['95'])).
% 27.57/27.77  thf('97', plain,
% 27.57/27.77      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77         (u1_struct_0 @ sk_C))
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_D))),
% 27.57/27.77      inference('sup+', [status(thm)], ['47', '96'])).
% 27.57/27.77  thf('98', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C)
% 27.57/27.77        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 27.57/27.77           (u1_struct_0 @ sk_C)))),
% 27.57/27.77      inference('simplify', [status(thm)], ['97'])).
% 27.57/27.77  thf('99', plain,
% 27.57/27.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 27.57/27.77         (~ (m1_pre_topc @ X19 @ X20)
% 27.57/27.77          | ~ (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 27.57/27.77          | (m1_pre_topc @ X19 @ X21)
% 27.57/27.77          | ~ (m1_pre_topc @ X21 @ X20)
% 27.57/27.77          | ~ (l1_pre_topc @ X20)
% 27.57/27.77          | ~ (v2_pre_topc @ X20))),
% 27.57/27.77      inference('cnf', [status(esa)], [t4_tsep_1])).
% 27.57/27.77  thf('100', plain,
% 27.57/27.77      (![X0 : $i]:
% 27.57/27.77         ((v2_struct_0 @ sk_C)
% 27.57/27.77          | (v2_struct_0 @ sk_A)
% 27.57/27.77          | (v2_struct_0 @ sk_B)
% 27.57/27.77          | (v2_struct_0 @ sk_D)
% 27.57/27.77          | ~ (v2_pre_topc @ X0)
% 27.57/27.77          | ~ (l1_pre_topc @ X0)
% 27.57/27.77          | ~ (m1_pre_topc @ sk_C @ X0)
% 27.57/27.77          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 27.57/27.77          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0))),
% 27.57/27.77      inference('sup-', [status(thm)], ['98', '99'])).
% 27.57/27.77  thf('101', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 27.57/27.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 27.57/27.77        | ~ (l1_pre_topc @ sk_A)
% 27.57/27.77        | ~ (v2_pre_topc @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('sup-', [status(thm)], ['7', '100'])).
% 27.57/27.77  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('105', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 27.57/27.77  thf('106', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C)
% 27.57/27.77        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_D))),
% 27.57/27.77      inference('simplify', [status(thm)], ['105'])).
% 27.57/27.77  thf('107', plain,
% 27.57/27.77      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('108', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_D)
% 27.57/27.77        | (v2_struct_0 @ sk_A)
% 27.57/27.77        | (v2_struct_0 @ sk_B)
% 27.57/27.77        | (v2_struct_0 @ sk_C))),
% 27.57/27.77      inference('sup-', [status(thm)], ['106', '107'])).
% 27.57/27.77  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('110', plain,
% 27.57/27.77      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 27.57/27.77      inference('sup-', [status(thm)], ['108', '109'])).
% 27.57/27.77  thf('111', plain, (~ (v2_struct_0 @ sk_C)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('112', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 27.57/27.77      inference('clc', [status(thm)], ['110', '111'])).
% 27.57/27.77  thf('113', plain, (~ (v2_struct_0 @ sk_D)),
% 27.57/27.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.57/27.77  thf('114', plain, ((v2_struct_0 @ sk_B)),
% 27.57/27.77      inference('clc', [status(thm)], ['112', '113'])).
% 27.57/27.77  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 27.57/27.77  
% 27.57/27.77  % SZS output end Refutation
% 27.57/27.77  
% 27.57/27.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
