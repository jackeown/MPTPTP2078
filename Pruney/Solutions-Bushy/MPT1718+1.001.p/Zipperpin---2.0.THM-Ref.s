%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1718+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dy3fhaALqC

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:08 EST 2020

% Result     : Theorem 17.21s
% Output     : Refutation 17.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 247 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   28
%              Number of atoms          : 1649 (5939 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t27_tmap_1,conjecture,(
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
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( m1_pre_topc @ B @ C )
                            & ( m1_pre_topc @ D @ E ) )
                         => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ ( k1_tsep_1 @ A @ C @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tmap_1])).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X6 ) @ X5 ) ) ),
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
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) @ sk_A ) ),
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

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( X2
       != ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ( ( u1_struct_0 @ X2 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) @ X1 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) @ X1 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X1 @ X0 @ X3 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('49',plain,
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
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
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
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('58',plain,
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
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['62'])).

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

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ( m1_pre_topc @ X11 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X13 )
      | ( r1_tarski @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_E )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X13 )
      | ( r1_tarski @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X1 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['76','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['66','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','96'])).

thf('98',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).


%------------------------------------------------------------------------------
