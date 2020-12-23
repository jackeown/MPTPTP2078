%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ADB3oP3xmR

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:29 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 633 expanded)
%              Number of leaves         :   23 ( 180 expanded)
%              Depth                    :   36
%              Number of atoms          : 2369 (12817 expanded)
%              Number of equality atoms :   46 (  79 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
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

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
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

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( X8
       != ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
      | ( ( u1_struct_0 @ X8 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) @ X7 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
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
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
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
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('28',plain,
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
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('47',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) @ X7 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X7 @ X6 @ X9 ) )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('48',plain,
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( k1_tsep_1 @ X17 @ X16 @ X16 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['93','94'])).

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

thf('96',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( k1_tsep_1 @ X14 @ X13 @ X15 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X13 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('97',plain,(
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['85','107'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('110',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['77','110'])).

thf('112',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ( m1_pre_topc @ X18 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ X1 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( k1_tsep_1 @ X17 @ X16 @ X16 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( k1_tsep_1 @ X14 @ X13 @ X15 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X13 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('148',plain,(
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
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['148'])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['136','158'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('160',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X1 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','161'])).

thf('163',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('165',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('169',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['162','169'])).

thf('171',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['118','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','171'])).

thf('173',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('175',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) )
    | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['173','179'])).

thf('181',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['77','110'])).

thf('182',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ( m1_pre_topc @ X18 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','186'])).

thf('188',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    $false ),
    inference(demod,[status(thm)],['0','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ADB3oP3xmR
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.01/1.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.22  % Solved by: fo/fo7.sh
% 1.01/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.22  % done 571 iterations in 0.740s
% 1.01/1.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.22  % SZS output start Refutation
% 1.01/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.01/1.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.01/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.22  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.22  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.01/1.22  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.01/1.22  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.22  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.01/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.22  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.01/1.22  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.01/1.22  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.01/1.22  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.01/1.22  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.01/1.22  thf(t29_tmap_1, conjecture,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.22           ( ![C:$i]:
% 1.01/1.22             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.01/1.22               ( ![D:$i]:
% 1.01/1.22                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.01/1.22                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 1.01/1.22                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 1.01/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.22    (~( ![A:$i]:
% 1.01/1.22        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.01/1.22            ( l1_pre_topc @ A ) ) =>
% 1.01/1.22          ( ![B:$i]:
% 1.01/1.22            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.22              ( ![C:$i]:
% 1.01/1.22                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.01/1.22                  ( ![D:$i]:
% 1.01/1.22                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.01/1.22                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 1.01/1.22                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 1.01/1.22    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 1.01/1.22  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(dt_k1_tsep_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.01/1.22         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.01/1.22         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.01/1.22       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.01/1.22         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.01/1.22         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.01/1.22  thf('3', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X10 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X10)
% 1.01/1.22          | ~ (l1_pre_topc @ X11)
% 1.01/1.22          | (v2_struct_0 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X12)
% 1.01/1.22          | ~ (m1_pre_topc @ X12 @ X11)
% 1.01/1.22          | (m1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12) @ X11))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.01/1.22  thf('4', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('6', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('7', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['1', '6'])).
% 1.01/1.22  thf('8', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['1', '6'])).
% 1.01/1.22  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('11', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X10 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X10)
% 1.01/1.22          | ~ (l1_pre_topc @ X11)
% 1.01/1.22          | (v2_struct_0 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X12)
% 1.01/1.22          | ~ (m1_pre_topc @ X12 @ X11)
% 1.01/1.22          | (v1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.01/1.22  thf('12', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['10', '11'])).
% 1.01/1.22  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('14', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 1.01/1.22  thf('15', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['9', '14'])).
% 1.01/1.22  thf('16', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['1', '6'])).
% 1.01/1.22  thf(d2_tsep_1, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.22           ( ![C:$i]:
% 1.01/1.22             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.01/1.22               ( ![D:$i]:
% 1.01/1.22                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.01/1.22                     ( m1_pre_topc @ D @ A ) ) =>
% 1.01/1.22                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.01/1.22                     ( ( u1_struct_0 @ D ) =
% 1.01/1.22                       ( k2_xboole_0 @
% 1.01/1.22                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.22  thf('17', plain,
% 1.01/1.22      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X6)
% 1.01/1.22          | ~ (m1_pre_topc @ X6 @ X7)
% 1.01/1.22          | (v2_struct_0 @ X8)
% 1.01/1.22          | ~ (v1_pre_topc @ X8)
% 1.01/1.22          | ~ (m1_pre_topc @ X8 @ X7)
% 1.01/1.22          | ((X8) != (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22          | ((u1_struct_0 @ X8)
% 1.01/1.22              = (k2_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X9)))
% 1.01/1.22          | ~ (m1_pre_topc @ X9 @ X7)
% 1.01/1.22          | (v2_struct_0 @ X9)
% 1.01/1.22          | ~ (l1_pre_topc @ X7)
% 1.01/1.22          | (v2_struct_0 @ X7))),
% 1.01/1.22      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.01/1.22  thf('18', plain,
% 1.01/1.22      (![X6 : $i, X7 : $i, X9 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X7)
% 1.01/1.22          | ~ (l1_pre_topc @ X7)
% 1.01/1.22          | (v2_struct_0 @ X9)
% 1.01/1.22          | ~ (m1_pre_topc @ X9 @ X7)
% 1.01/1.22          | ((u1_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22              = (k2_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X9)))
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9) @ X7)
% 1.01/1.22          | ~ (v1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22          | (v2_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22          | ~ (m1_pre_topc @ X6 @ X7)
% 1.01/1.22          | (v2_struct_0 @ X6))),
% 1.01/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.01/1.22  thf('19', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['16', '18'])).
% 1.01/1.22  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('23', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 1.01/1.22  thf('24', plain,
% 1.01/1.22      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('simplify', [status(thm)], ['23'])).
% 1.01/1.22  thf('25', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['15', '24'])).
% 1.01/1.22  thf('26', plain,
% 1.01/1.22      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('simplify', [status(thm)], ['25'])).
% 1.01/1.22  thf('27', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X10 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X10)
% 1.01/1.22          | ~ (l1_pre_topc @ X11)
% 1.01/1.22          | (v2_struct_0 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X12)
% 1.01/1.22          | ~ (m1_pre_topc @ X12 @ X11)
% 1.01/1.22          | ~ (v2_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.01/1.22  thf('28', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.01/1.22  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('32', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.01/1.22  thf('33', plain,
% 1.01/1.22      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 1.01/1.22          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('simplify', [status(thm)], ['32'])).
% 1.01/1.22  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('36', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X10 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X10)
% 1.01/1.22          | ~ (l1_pre_topc @ X11)
% 1.01/1.22          | (v2_struct_0 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X12)
% 1.01/1.22          | ~ (m1_pre_topc @ X12 @ X11)
% 1.01/1.22          | (m1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12) @ X11))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.01/1.22  thf('37', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['35', '36'])).
% 1.01/1.22  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('39', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0) @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['37', '38'])).
% 1.01/1.22  thf('40', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['34', '39'])).
% 1.01/1.22  thf('41', plain,
% 1.01/1.22      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('simplify', [status(thm)], ['40'])).
% 1.01/1.22  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('43', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A))),
% 1.01/1.22      inference('clc', [status(thm)], ['41', '42'])).
% 1.01/1.22  thf('44', plain, (~ (v2_struct_0 @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('45', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)),
% 1.01/1.22      inference('clc', [status(thm)], ['43', '44'])).
% 1.01/1.22  thf('46', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)),
% 1.01/1.22      inference('clc', [status(thm)], ['43', '44'])).
% 1.01/1.22  thf('47', plain,
% 1.01/1.22      (![X6 : $i, X7 : $i, X9 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X7)
% 1.01/1.22          | ~ (l1_pre_topc @ X7)
% 1.01/1.22          | (v2_struct_0 @ X9)
% 1.01/1.22          | ~ (m1_pre_topc @ X9 @ X7)
% 1.01/1.22          | ((u1_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22              = (k2_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X9)))
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9) @ X7)
% 1.01/1.22          | ~ (v1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22          | (v2_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 1.01/1.22          | ~ (m1_pre_topc @ X6 @ X7)
% 1.01/1.22          | (v2_struct_0 @ X6))),
% 1.01/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.01/1.22  thf('48', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['46', '47'])).
% 1.01/1.22  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('50', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('52', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 1.01/1.22  thf('53', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('simplify', [status(thm)], ['52'])).
% 1.01/1.22  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('56', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X10 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X10)
% 1.01/1.22          | ~ (l1_pre_topc @ X11)
% 1.01/1.22          | (v2_struct_0 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X12)
% 1.01/1.22          | ~ (m1_pre_topc @ X12 @ X11)
% 1.01/1.22          | (v1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.01/1.22  thf('57', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['55', '56'])).
% 1.01/1.22  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('59', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ X0)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['57', '58'])).
% 1.01/1.22  thf('60', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['54', '59'])).
% 1.01/1.22  thf('61', plain,
% 1.01/1.22      (((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('simplify', [status(thm)], ['60'])).
% 1.01/1.22  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('63', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C) | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 1.01/1.22      inference('clc', [status(thm)], ['61', '62'])).
% 1.01/1.22  thf('64', plain, (~ (v2_struct_0 @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('65', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 1.01/1.22      inference('clc', [status(thm)], ['63', '64'])).
% 1.01/1.22  thf('66', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['53', '65'])).
% 1.01/1.22  thf('67', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X10 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X10)
% 1.01/1.22          | ~ (l1_pre_topc @ X11)
% 1.01/1.22          | (v2_struct_0 @ X11)
% 1.01/1.22          | (v2_struct_0 @ X12)
% 1.01/1.22          | ~ (m1_pre_topc @ X12 @ X11)
% 1.01/1.22          | ~ (v2_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.01/1.22  thf('68', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['66', '67'])).
% 1.01/1.22  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('71', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('72', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 1.01/1.22  thf('73', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('simplify', [status(thm)], ['72'])).
% 1.01/1.22  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('75', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))))),
% 1.01/1.22      inference('clc', [status(thm)], ['73', '74'])).
% 1.01/1.22  thf('76', plain, (~ (v2_struct_0 @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('77', plain,
% 1.01/1.22      (((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22         = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('clc', [status(thm)], ['75', '76'])).
% 1.01/1.22  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('79', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(t4_tsep_1, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( m1_pre_topc @ B @ A ) =>
% 1.01/1.22           ( ![C:$i]:
% 1.01/1.22             ( ( m1_pre_topc @ C @ A ) =>
% 1.01/1.22               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.01/1.22                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.01/1.22  thf('80', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X18 @ X19)
% 1.01/1.22          | ~ (m1_pre_topc @ X18 @ X20)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.01/1.22          | ~ (m1_pre_topc @ X20 @ X19)
% 1.01/1.22          | ~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (v2_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.01/1.22  thf('81', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (v2_pre_topc @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['79', '80'])).
% 1.01/1.22  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('84', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.01/1.22  thf('85', plain,
% 1.01/1.22      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 1.01/1.22        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['78', '84'])).
% 1.01/1.22  thf('86', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(t25_tmap_1, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.22           ( ( k1_tsep_1 @ A @ B @ B ) =
% 1.01/1.22             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 1.01/1.22  thf('87', plain,
% 1.01/1.22      (![X16 : $i, X17 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X16)
% 1.01/1.22          | ~ (m1_pre_topc @ X16 @ X17)
% 1.01/1.22          | ((k1_tsep_1 @ X17 @ X16 @ X16)
% 1.01/1.22              = (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 1.01/1.22          | ~ (l1_pre_topc @ X17)
% 1.01/1.22          | ~ (v2_pre_topc @ X17)
% 1.01/1.22          | (v2_struct_0 @ X17))),
% 1.01/1.22      inference('cnf', [status(esa)], [t25_tmap_1])).
% 1.01/1.22  thf('88', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 1.01/1.22            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['86', '87'])).
% 1.01/1.22  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('91', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 1.01/1.22            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.01/1.22  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('93', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 1.01/1.22            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 1.01/1.22      inference('clc', [status(thm)], ['91', '92'])).
% 1.01/1.22  thf('94', plain, (~ (v2_struct_0 @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('95', plain,
% 1.01/1.22      (((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 1.01/1.22         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 1.01/1.22      inference('clc', [status(thm)], ['93', '94'])).
% 1.01/1.22  thf(t23_tsep_1, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.01/1.22           ( ![C:$i]:
% 1.01/1.22             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.01/1.22               ( ( m1_pre_topc @ B @ C ) <=>
% 1.01/1.22                 ( ( k1_tsep_1 @ A @ B @ C ) =
% 1.01/1.22                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 1.01/1.22  thf('96', plain,
% 1.01/1.22      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X13)
% 1.01/1.22          | ~ (m1_pre_topc @ X13 @ X14)
% 1.01/1.22          | ((k1_tsep_1 @ X14 @ X13 @ X15)
% 1.01/1.22              != (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 1.01/1.22          | (m1_pre_topc @ X13 @ X15)
% 1.01/1.22          | ~ (m1_pre_topc @ X15 @ X14)
% 1.01/1.22          | (v2_struct_0 @ X15)
% 1.01/1.22          | ~ (l1_pre_topc @ X14)
% 1.01/1.22          | ~ (v2_pre_topc @ X14)
% 1.01/1.22          | (v2_struct_0 @ X14))),
% 1.01/1.22      inference('cnf', [status(esa)], [t23_tsep_1])).
% 1.01/1.22  thf('97', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (((k1_tsep_1 @ X1 @ X0 @ sk_C) != (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22          | (v2_struct_0 @ X1)
% 1.01/1.22          | ~ (v2_pre_topc @ X1)
% 1.01/1.22          | ~ (l1_pre_topc @ X1)
% 1.01/1.22          | (v2_struct_0 @ sk_C)
% 1.01/1.22          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.01/1.22          | (m1_pre_topc @ X0 @ sk_C)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ X1)
% 1.01/1.22          | (v2_struct_0 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['95', '96'])).
% 1.01/1.22  thf('98', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_C)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | (m1_pre_topc @ sk_C @ sk_C)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('eq_res', [status(thm)], ['97'])).
% 1.01/1.22  thf('99', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | (m1_pre_topc @ sk_C @ sk_C)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('simplify', [status(thm)], ['98'])).
% 1.01/1.22  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('103', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | (m1_pre_topc @ sk_C @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 1.01/1.22  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('105', plain, (((v2_struct_0 @ sk_C) | (m1_pre_topc @ sk_C @ sk_C))),
% 1.01/1.22      inference('clc', [status(thm)], ['103', '104'])).
% 1.01/1.22  thf('106', plain, (~ (v2_struct_0 @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('107', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.01/1.22      inference('clc', [status(thm)], ['105', '106'])).
% 1.01/1.22  thf('108', plain,
% 1.01/1.22      ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['85', '107'])).
% 1.01/1.22  thf(t12_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.01/1.22  thf('109', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.01/1.22  thf('110', plain,
% 1.01/1.22      (((k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 1.01/1.22         = (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['108', '109'])).
% 1.01/1.22  thf('111', plain,
% 1.01/1.22      (((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)) = (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['77', '110'])).
% 1.01/1.22  thf('112', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X18 @ X19)
% 1.01/1.22          | ~ (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.01/1.22          | (m1_pre_topc @ X18 @ X20)
% 1.01/1.22          | ~ (m1_pre_topc @ X20 @ X19)
% 1.01/1.22          | ~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (v2_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.01/1.22  thf('113', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C))
% 1.01/1.22          | ~ (v2_pre_topc @ X1)
% 1.01/1.22          | ~ (l1_pre_topc @ X1)
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ X1)
% 1.01/1.22          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.01/1.22      inference('sup-', [status(thm)], ['111', '112'])).
% 1.01/1.22  thf('114', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['45', '113'])).
% 1.01/1.22  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('117', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.01/1.22  thf('118', plain,
% 1.01/1.22      ((~ (r1_tarski @ 
% 1.01/1.22           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 1.01/1.22           (u1_struct_0 @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 1.01/1.22           (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['33', '117'])).
% 1.01/1.22  thf('119', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('120', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('121', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X18 @ X19)
% 1.01/1.22          | ~ (m1_pre_topc @ X18 @ X20)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.01/1.22          | ~ (m1_pre_topc @ X20 @ X19)
% 1.01/1.22          | ~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (v2_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.01/1.22  thf('122', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (v2_pre_topc @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_D @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['120', '121'])).
% 1.01/1.22  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('125', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_D @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.01/1.22  thf('126', plain,
% 1.01/1.22      ((~ (m1_pre_topc @ sk_D @ sk_C)
% 1.01/1.22        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['119', '125'])).
% 1.01/1.22  thf('127', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('128', plain,
% 1.01/1.22      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['126', '127'])).
% 1.01/1.22  thf('129', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('130', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('131', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X18 @ X19)
% 1.01/1.22          | ~ (m1_pre_topc @ X18 @ X20)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.01/1.22          | ~ (m1_pre_topc @ X20 @ X19)
% 1.01/1.22          | ~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (v2_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.01/1.22  thf('132', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (v2_pre_topc @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['130', '131'])).
% 1.01/1.22  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('135', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['132', '133', '134'])).
% 1.01/1.22  thf('136', plain,
% 1.01/1.22      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 1.01/1.22        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['129', '135'])).
% 1.01/1.22  thf('137', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('138', plain,
% 1.01/1.22      (![X16 : $i, X17 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X16)
% 1.01/1.22          | ~ (m1_pre_topc @ X16 @ X17)
% 1.01/1.22          | ((k1_tsep_1 @ X17 @ X16 @ X16)
% 1.01/1.22              = (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 1.01/1.22          | ~ (l1_pre_topc @ X17)
% 1.01/1.22          | ~ (v2_pre_topc @ X17)
% 1.01/1.22          | (v2_struct_0 @ X17))),
% 1.01/1.22      inference('cnf', [status(esa)], [t25_tmap_1])).
% 1.01/1.22  thf('139', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 1.01/1.22            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.01/1.22        | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['137', '138'])).
% 1.01/1.22  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('142', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 1.01/1.22            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 1.01/1.22        | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['139', '140', '141'])).
% 1.01/1.22  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('144', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | ((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 1.01/1.22            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 1.01/1.22      inference('clc', [status(thm)], ['142', '143'])).
% 1.01/1.22  thf('145', plain, (~ (v2_struct_0 @ sk_B)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('146', plain,
% 1.01/1.22      (((k1_tsep_1 @ sk_A @ sk_B @ sk_B)
% 1.01/1.22         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 1.01/1.22      inference('clc', [status(thm)], ['144', '145'])).
% 1.01/1.22  thf('147', plain,
% 1.01/1.22      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.01/1.22         ((v2_struct_0 @ X13)
% 1.01/1.22          | ~ (m1_pre_topc @ X13 @ X14)
% 1.01/1.22          | ((k1_tsep_1 @ X14 @ X13 @ X15)
% 1.01/1.22              != (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 1.01/1.22          | (m1_pre_topc @ X13 @ X15)
% 1.01/1.22          | ~ (m1_pre_topc @ X15 @ X14)
% 1.01/1.22          | (v2_struct_0 @ X15)
% 1.01/1.22          | ~ (l1_pre_topc @ X14)
% 1.01/1.22          | ~ (v2_pre_topc @ X14)
% 1.01/1.22          | (v2_struct_0 @ X14))),
% 1.01/1.22      inference('cnf', [status(esa)], [t23_tsep_1])).
% 1.01/1.22  thf('148', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (((k1_tsep_1 @ X1 @ X0 @ sk_B) != (k1_tsep_1 @ sk_A @ sk_B @ sk_B))
% 1.01/1.22          | (v2_struct_0 @ X1)
% 1.01/1.22          | ~ (v2_pre_topc @ X1)
% 1.01/1.22          | ~ (l1_pre_topc @ X1)
% 1.01/1.22          | (v2_struct_0 @ sk_B)
% 1.01/1.22          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.01/1.22          | (m1_pre_topc @ X0 @ sk_B)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ X1)
% 1.01/1.22          | (v2_struct_0 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['146', '147'])).
% 1.01/1.22  thf('149', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.01/1.22        | (m1_pre_topc @ sk_B @ sk_B)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('eq_res', [status(thm)], ['148'])).
% 1.01/1.22  thf('150', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | (m1_pre_topc @ sk_B @ sk_B)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('simplify', [status(thm)], ['149'])).
% 1.01/1.22  thf('151', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('153', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('154', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_A)
% 1.01/1.22        | (m1_pre_topc @ sk_B @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 1.01/1.22  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('156', plain, (((v2_struct_0 @ sk_B) | (m1_pre_topc @ sk_B @ sk_B))),
% 1.01/1.22      inference('clc', [status(thm)], ['154', '155'])).
% 1.01/1.22  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('158', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.01/1.22      inference('clc', [status(thm)], ['156', '157'])).
% 1.01/1.22  thf('159', plain,
% 1.01/1.22      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['136', '158'])).
% 1.01/1.22  thf(t13_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.22     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 1.01/1.22       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 1.01/1.22  thf('160', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X2 @ X3)
% 1.01/1.22          | ~ (r1_tarski @ X4 @ X5)
% 1.01/1.22          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ (k2_xboole_0 @ X3 @ X5)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t13_xboole_1])).
% 1.01/1.22  thf('161', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((r1_tarski @ (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X1) @ 
% 1.01/1.22           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))
% 1.01/1.22          | ~ (r1_tarski @ X1 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['159', '160'])).
% 1.01/1.22  thf('162', plain,
% 1.01/1.22      ((r1_tarski @ 
% 1.01/1.22        (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 1.01/1.22        (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['128', '161'])).
% 1.01/1.22  thf('163', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('164', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['132', '133', '134'])).
% 1.01/1.22  thf('165', plain,
% 1.01/1.22      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 1.01/1.22        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['163', '164'])).
% 1.01/1.22  thf('166', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('167', plain,
% 1.01/1.22      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['165', '166'])).
% 1.01/1.22  thf('168', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.01/1.22  thf('169', plain,
% 1.01/1.22      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 1.01/1.22         = (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['167', '168'])).
% 1.01/1.22  thf('170', plain,
% 1.01/1.22      ((r1_tarski @ 
% 1.01/1.22        (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 1.01/1.22        (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['162', '169'])).
% 1.01/1.22  thf('171', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 1.01/1.22           (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['118', '170'])).
% 1.01/1.22  thf('172', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 1.01/1.22           (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('sup-', [status(thm)], ['8', '171'])).
% 1.01/1.22  thf('173', plain,
% 1.01/1.22      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ 
% 1.01/1.22         (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('simplify', [status(thm)], ['172'])).
% 1.01/1.22  thf('174', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['1', '6'])).
% 1.01/1.22  thf('175', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X18 @ X19)
% 1.01/1.22          | ~ (m1_pre_topc @ X18 @ X20)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.01/1.22          | ~ (m1_pre_topc @ X20 @ X19)
% 1.01/1.22          | ~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (v2_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.01/1.22  thf('176', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v2_struct_0 @ sk_D)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B)
% 1.01/1.22          | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 1.01/1.22             (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['174', '175'])).
% 1.01/1.22  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('179', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v2_struct_0 @ sk_D)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B)
% 1.01/1.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.01/1.22          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 1.01/1.22             (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['176', '177', '178'])).
% 1.01/1.22  thf('180', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 1.01/1.22           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))
% 1.01/1.22        | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('sup-', [status(thm)], ['173', '179'])).
% 1.01/1.22  thf('181', plain,
% 1.01/1.22      (((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)) = (u1_struct_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['77', '110'])).
% 1.01/1.22  thf('182', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C) @ sk_A)),
% 1.01/1.22      inference('clc', [status(thm)], ['43', '44'])).
% 1.01/1.22  thf('183', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 1.01/1.22           (u1_struct_0 @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.01/1.22  thf('184', plain,
% 1.01/1.22      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)) @ 
% 1.01/1.22         (u1_struct_0 @ sk_C))
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('simplify', [status(thm)], ['183'])).
% 1.01/1.22  thf('185', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X18 @ X19)
% 1.01/1.22          | ~ (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.01/1.22          | (m1_pre_topc @ X18 @ X20)
% 1.01/1.22          | ~ (m1_pre_topc @ X20 @ X19)
% 1.01/1.22          | ~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (v2_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.01/1.22  thf('186', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v2_struct_0 @ sk_D)
% 1.01/1.22          | (v2_struct_0 @ sk_A)
% 1.01/1.22          | (v2_struct_0 @ sk_B)
% 1.01/1.22          | ~ (v2_pre_topc @ X0)
% 1.01/1.22          | ~ (l1_pre_topc @ X0)
% 1.01/1.22          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.01/1.22          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['184', '185'])).
% 1.01/1.22  thf('187', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 1.01/1.22        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.01/1.22        | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('sup-', [status(thm)], ['7', '186'])).
% 1.01/1.22  thf('188', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('190', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('191', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 1.01/1.22  thf('192', plain,
% 1.01/1.22      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 1.01/1.22        | (v2_struct_0 @ sk_B)
% 1.01/1.22        | (v2_struct_0 @ sk_A)
% 1.01/1.22        | (v2_struct_0 @ sk_D))),
% 1.01/1.22      inference('simplify', [status(thm)], ['191'])).
% 1.01/1.22  thf('193', plain,
% 1.01/1.22      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('194', plain,
% 1.01/1.22      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['192', '193'])).
% 1.01/1.22  thf('195', plain, (~ (v2_struct_0 @ sk_D)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('196', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 1.01/1.22      inference('clc', [status(thm)], ['194', '195'])).
% 1.01/1.22  thf('197', plain, (~ (v2_struct_0 @ sk_B)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('198', plain, ((v2_struct_0 @ sk_A)),
% 1.01/1.22      inference('clc', [status(thm)], ['196', '197'])).
% 1.01/1.22  thf('199', plain, ($false), inference('demod', [status(thm)], ['0', '198'])).
% 1.01/1.22  
% 1.01/1.22  % SZS output end Refutation
% 1.01/1.22  
% 1.06/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
