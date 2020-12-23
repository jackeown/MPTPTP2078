%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VgeX49sr3B

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:30 EST 2020

% Result     : Theorem 17.58s
% Output     : Refutation 17.58s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 307 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   27
%              Number of atoms          : 1708 (6338 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) @ X12 ) ) ),
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
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
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
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ X0 ) @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ X0 ) @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['19','24'])).

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

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( r1_tsep_1 @ X7 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( X10
       != ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
      | ( ( u1_struct_0 @ X10 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) @ X8 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
      | ( r1_tsep_1 @ X7 @ X9 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) @ sk_D ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) )
      | ( m1_pre_topc @ X14 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) @ X8 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) )
      | ( r1_tsep_1 @ X7 @ X9 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('79',plain,
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
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
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
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
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
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('88',plain,
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
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) )
      | ( m1_pre_topc @ X14 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','97'])).

thf('99',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VgeX49sr3B
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 17.58/17.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.58/17.77  % Solved by: fo/fo7.sh
% 17.58/17.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.58/17.77  % done 9821 iterations in 17.311s
% 17.58/17.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.58/17.77  % SZS output start Refutation
% 17.58/17.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.58/17.77  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 17.58/17.77  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 17.58/17.77  thf(sk_C_type, type, sk_C: $i).
% 17.58/17.77  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 17.58/17.77  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 17.58/17.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.58/17.77  thf(sk_D_type, type, sk_D: $i).
% 17.58/17.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 17.58/17.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.58/17.77  thf(sk_A_type, type, sk_A: $i).
% 17.58/17.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.58/17.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 17.58/17.77  thf(sk_B_type, type, sk_B: $i).
% 17.58/17.77  thf(t30_tmap_1, conjecture,
% 17.58/17.77    (![A:$i]:
% 17.58/17.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.58/17.77       ( ![B:$i]:
% 17.58/17.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 17.58/17.77           ( ![C:$i]:
% 17.58/17.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 17.58/17.77               ( ![D:$i]:
% 17.58/17.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 17.58/17.77                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 17.58/17.77                     ( ( r1_tsep_1 @ B @ C ) | 
% 17.58/17.77                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 17.58/17.77  thf(zf_stmt_0, negated_conjecture,
% 17.58/17.77    (~( ![A:$i]:
% 17.58/17.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 17.58/17.77            ( l1_pre_topc @ A ) ) =>
% 17.58/17.77          ( ![B:$i]:
% 17.58/17.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 17.58/17.77              ( ![C:$i]:
% 17.58/17.77                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 17.58/17.77                  ( ![D:$i]:
% 17.58/17.77                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 17.58/17.77                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 17.58/17.77                        ( ( r1_tsep_1 @ B @ C ) | 
% 17.58/17.77                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 17.58/17.77    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 17.58/17.77  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf(dt_k2_tsep_1, axiom,
% 17.58/17.77    (![A:$i,B:$i,C:$i]:
% 17.58/17.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 17.58/17.77         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 17.58/17.77         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 17.58/17.77       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 17.58/17.77         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 17.58/17.77         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 17.58/17.77  thf('3', plain,
% 17.58/17.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X11 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X11)
% 17.58/17.77          | ~ (l1_pre_topc @ X12)
% 17.58/17.77          | (v2_struct_0 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X13)
% 17.58/17.77          | ~ (m1_pre_topc @ X13 @ X12)
% 17.58/17.77          | (m1_pre_topc @ (k2_tsep_1 @ X12 @ X11 @ X13) @ X12))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 17.58/17.77  thf('4', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_A)
% 17.58/17.77          | ~ (l1_pre_topc @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('sup-', [status(thm)], ['2', '3'])).
% 17.58/17.77  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('6', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('demod', [status(thm)], ['4', '5'])).
% 17.58/17.77  thf('7', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 17.58/17.77      inference('sup-', [status(thm)], ['1', '6'])).
% 17.58/17.77  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('10', plain,
% 17.58/17.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X11 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X11)
% 17.58/17.77          | ~ (l1_pre_topc @ X12)
% 17.58/17.77          | (v2_struct_0 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X13)
% 17.58/17.77          | ~ (m1_pre_topc @ X13 @ X12)
% 17.58/17.77          | (v1_pre_topc @ (k2_tsep_1 @ X12 @ X11 @ X13)))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 17.58/17.77  thf('11', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0))
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | ~ (l1_pre_topc @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('sup-', [status(thm)], ['9', '10'])).
% 17.58/17.77  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf(dt_m1_pre_topc, axiom,
% 17.58/17.77    (![A:$i]:
% 17.58/17.77     ( ( l1_pre_topc @ A ) =>
% 17.58/17.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 17.58/17.77  thf('13', plain,
% 17.58/17.77      (![X5 : $i, X6 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 17.58/17.77  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['12', '13'])).
% 17.58/17.77  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['14', '15'])).
% 17.58/17.77  thf('17', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0))
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('demod', [status(thm)], ['11', '16'])).
% 17.58/17.77  thf('18', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)))),
% 17.58/17.77      inference('sup-', [status(thm)], ['8', '17'])).
% 17.58/17.77  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('21', plain,
% 17.58/17.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X11 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X11)
% 17.58/17.77          | ~ (l1_pre_topc @ X12)
% 17.58/17.77          | (v2_struct_0 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X13)
% 17.58/17.77          | ~ (m1_pre_topc @ X13 @ X12)
% 17.58/17.77          | (m1_pre_topc @ (k2_tsep_1 @ X12 @ X11 @ X13) @ X12))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 17.58/17.77  thf('22', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0) @ sk_D)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | ~ (l1_pre_topc @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('sup-', [status(thm)], ['20', '21'])).
% 17.58/17.77  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['14', '15'])).
% 17.58/17.77  thf('24', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0) @ sk_D)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('demod', [status(thm)], ['22', '23'])).
% 17.58/17.77  thf('25', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['19', '24'])).
% 17.58/17.77  thf(d5_tsep_1, axiom,
% 17.58/17.77    (![A:$i]:
% 17.58/17.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 17.58/17.77       ( ![B:$i]:
% 17.58/17.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 17.58/17.77           ( ![C:$i]:
% 17.58/17.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 17.58/17.77               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 17.58/17.77                 ( ![D:$i]:
% 17.58/17.77                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 17.58/17.77                       ( m1_pre_topc @ D @ A ) ) =>
% 17.58/17.77                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 17.58/17.77                       ( ( u1_struct_0 @ D ) =
% 17.58/17.77                         ( k3_xboole_0 @
% 17.58/17.77                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 17.58/17.77  thf('26', plain,
% 17.58/17.77      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 17.58/17.77         ((v2_struct_0 @ X7)
% 17.58/17.77          | ~ (m1_pre_topc @ X7 @ X8)
% 17.58/17.77          | (r1_tsep_1 @ X7 @ X9)
% 17.58/17.77          | (v2_struct_0 @ X10)
% 17.58/17.77          | ~ (v1_pre_topc @ X10)
% 17.58/17.77          | ~ (m1_pre_topc @ X10 @ X8)
% 17.58/17.77          | ((X10) != (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77          | ((u1_struct_0 @ X10)
% 17.58/17.77              = (k3_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X9)))
% 17.58/17.77          | ~ (m1_pre_topc @ X9 @ X8)
% 17.58/17.77          | (v2_struct_0 @ X9)
% 17.58/17.77          | ~ (l1_pre_topc @ X8)
% 17.58/17.77          | (v2_struct_0 @ X8))),
% 17.58/17.77      inference('cnf', [status(esa)], [d5_tsep_1])).
% 17.58/17.77  thf('27', plain,
% 17.58/17.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 17.58/17.77         ((v2_struct_0 @ X8)
% 17.58/17.77          | ~ (l1_pre_topc @ X8)
% 17.58/17.77          | (v2_struct_0 @ X9)
% 17.58/17.77          | ~ (m1_pre_topc @ X9 @ X8)
% 17.58/17.77          | ((u1_struct_0 @ (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77              = (k3_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X9)))
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X9) @ X8)
% 17.58/17.77          | ~ (v1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77          | (v2_struct_0 @ (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77          | (r1_tsep_1 @ X7 @ X9)
% 17.58/17.77          | ~ (m1_pre_topc @ X7 @ X8)
% 17.58/17.77          | (v2_struct_0 @ X7))),
% 17.58/17.77      inference('simplify', [status(thm)], ['26'])).
% 17.58/17.77  thf('28', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | ~ (m1_pre_topc @ sk_B @ sk_D)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | ~ (l1_pre_topc @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['25', '27'])).
% 17.58/17.77  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['14', '15'])).
% 17.58/17.77  thf('32', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D))),
% 17.58/17.77      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 17.58/17.77  thf('33', plain,
% 17.58/17.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['32'])).
% 17.58/17.77  thf('34', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 17.58/17.77      inference('sup-', [status(thm)], ['18', '33'])).
% 17.58/17.77  thf('35', plain,
% 17.58/17.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['34'])).
% 17.58/17.77  thf('36', plain,
% 17.58/17.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X11 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X11)
% 17.58/17.77          | ~ (l1_pre_topc @ X12)
% 17.58/17.77          | (v2_struct_0 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X13)
% 17.58/17.77          | ~ (m1_pre_topc @ X13 @ X12)
% 17.58/17.77          | ~ (v2_struct_0 @ (k2_tsep_1 @ X12 @ X11 @ X13)))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 17.58/17.77  thf('37', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | ~ (l1_pre_topc @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | ~ (m1_pre_topc @ sk_B @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['35', '36'])).
% 17.58/17.77  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['14', '15'])).
% 17.58/17.77  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('41', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 17.58/17.77  thf('42', plain,
% 17.58/17.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 17.58/17.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['41'])).
% 17.58/17.77  thf('43', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['19', '24'])).
% 17.58/17.77  thf('44', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['19', '24'])).
% 17.58/17.77  thf(t4_tsep_1, axiom,
% 17.58/17.77    (![A:$i]:
% 17.58/17.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.58/17.77       ( ![B:$i]:
% 17.58/17.77         ( ( m1_pre_topc @ B @ A ) =>
% 17.58/17.77           ( ![C:$i]:
% 17.58/17.77             ( ( m1_pre_topc @ C @ A ) =>
% 17.58/17.77               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 17.58/17.77                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 17.58/17.77  thf('45', plain,
% 17.58/17.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X14 @ X15)
% 17.58/17.77          | ~ (m1_pre_topc @ X14 @ X16)
% 17.58/17.77          | (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 17.58/17.77          | ~ (m1_pre_topc @ X16 @ X15)
% 17.58/17.77          | ~ (l1_pre_topc @ X15)
% 17.58/17.77          | ~ (v2_pre_topc @ X15))),
% 17.58/17.77      inference('cnf', [status(esa)], [t4_tsep_1])).
% 17.58/17.77  thf('46', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v2_struct_0 @ sk_C)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B)
% 17.58/17.77          | ~ (v2_pre_topc @ sk_D)
% 17.58/17.77          | ~ (l1_pre_topc @ sk_D)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 17.58/17.77          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 17.58/17.77             (u1_struct_0 @ X0))
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ X0))),
% 17.58/17.77      inference('sup-', [status(thm)], ['44', '45'])).
% 17.58/17.77  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf(cc1_pre_topc, axiom,
% 17.58/17.77    (![A:$i]:
% 17.58/17.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.58/17.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 17.58/17.77  thf('48', plain,
% 17.58/17.77      (![X3 : $i, X4 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X3 @ X4)
% 17.58/17.77          | (v2_pre_topc @ X3)
% 17.58/17.77          | ~ (l1_pre_topc @ X4)
% 17.58/17.77          | ~ (v2_pre_topc @ X4))),
% 17.58/17.77      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 17.58/17.77  thf('49', plain,
% 17.58/17.77      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['47', '48'])).
% 17.58/17.77  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('52', plain, ((v2_pre_topc @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['49', '50', '51'])).
% 17.58/17.77  thf('53', plain, ((l1_pre_topc @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['14', '15'])).
% 17.58/17.77  thf('54', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v2_struct_0 @ sk_C)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 17.58/17.77          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 17.58/17.77             (u1_struct_0 @ X0))
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ X0))),
% 17.58/17.77      inference('demod', [status(thm)], ['46', '52', '53'])).
% 17.58/17.77  thf('55', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 17.58/17.77           (u1_struct_0 @ sk_D))
% 17.58/17.77        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('sup-', [status(thm)], ['43', '54'])).
% 17.58/17.77  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf(d10_xboole_0, axiom,
% 17.58/17.77    (![A:$i,B:$i]:
% 17.58/17.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 17.58/17.77  thf('57', plain,
% 17.58/17.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 17.58/17.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.58/17.77  thf('58', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 17.58/17.77      inference('simplify', [status(thm)], ['57'])).
% 17.58/17.77  thf('59', plain,
% 17.58/17.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X14 @ X15)
% 17.58/17.77          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 17.58/17.77          | (m1_pre_topc @ X14 @ X16)
% 17.58/17.77          | ~ (m1_pre_topc @ X16 @ X15)
% 17.58/17.77          | ~ (l1_pre_topc @ X15)
% 17.58/17.77          | ~ (v2_pre_topc @ X15))),
% 17.58/17.77      inference('cnf', [status(esa)], [t4_tsep_1])).
% 17.58/17.77  thf('60', plain,
% 17.58/17.77      (![X0 : $i, X1 : $i]:
% 17.58/17.77         (~ (v2_pre_topc @ X1)
% 17.58/17.77          | ~ (l1_pre_topc @ X1)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ X1)
% 17.58/17.77          | (m1_pre_topc @ X0 @ X0)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 17.58/17.77      inference('sup-', [status(thm)], ['58', '59'])).
% 17.58/17.77  thf('61', plain,
% 17.58/17.77      (![X0 : $i, X1 : $i]:
% 17.58/17.77         ((m1_pre_topc @ X0 @ X0)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ X1)
% 17.58/17.77          | ~ (l1_pre_topc @ X1)
% 17.58/17.77          | ~ (v2_pre_topc @ X1))),
% 17.58/17.77      inference('simplify', [status(thm)], ['60'])).
% 17.58/17.77  thf('62', plain,
% 17.58/17.77      ((~ (v2_pre_topc @ sk_A)
% 17.58/17.77        | ~ (l1_pre_topc @ sk_A)
% 17.58/17.77        | (m1_pre_topc @ sk_D @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['56', '61'])).
% 17.58/17.77  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('65', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 17.58/17.77      inference('demod', [status(thm)], ['62', '63', '64'])).
% 17.58/17.77  thf('66', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 17.58/17.77           (u1_struct_0 @ sk_D))
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('demod', [status(thm)], ['55', '65'])).
% 17.58/17.77  thf('67', plain,
% 17.58/17.77      (((r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 17.58/17.77         (u1_struct_0 @ sk_D))
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['66'])).
% 17.58/17.77  thf('68', plain,
% 17.58/17.77      (((r1_tarski @ 
% 17.58/17.77         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 17.58/17.77         (u1_struct_0 @ sk_D))
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('sup+', [status(thm)], ['42', '67'])).
% 17.58/17.77  thf('69', plain,
% 17.58/17.77      (((r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (r1_tarski @ 
% 17.58/17.77           (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 17.58/17.77           (u1_struct_0 @ sk_D)))),
% 17.58/17.77      inference('simplify', [status(thm)], ['68'])).
% 17.58/17.77  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('72', plain,
% 17.58/17.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X11 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X11)
% 17.58/17.77          | ~ (l1_pre_topc @ X12)
% 17.58/17.77          | (v2_struct_0 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X13)
% 17.58/17.77          | ~ (m1_pre_topc @ X13 @ X12)
% 17.58/17.77          | (v1_pre_topc @ (k2_tsep_1 @ X12 @ X11 @ X13)))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 17.58/17.77  thf('73', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_A)
% 17.58/17.77          | ~ (l1_pre_topc @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('sup-', [status(thm)], ['71', '72'])).
% 17.58/17.77  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('75', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ X0)
% 17.58/17.77          | (v2_struct_0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('demod', [status(thm)], ['73', '74'])).
% 17.58/17.77  thf('76', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 17.58/17.77      inference('sup-', [status(thm)], ['70', '75'])).
% 17.58/17.77  thf('77', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 17.58/17.77      inference('sup-', [status(thm)], ['1', '6'])).
% 17.58/17.77  thf('78', plain,
% 17.58/17.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 17.58/17.77         ((v2_struct_0 @ X8)
% 17.58/17.77          | ~ (l1_pre_topc @ X8)
% 17.58/17.77          | (v2_struct_0 @ X9)
% 17.58/17.77          | ~ (m1_pre_topc @ X9 @ X8)
% 17.58/17.77          | ((u1_struct_0 @ (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77              = (k3_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X9)))
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X9) @ X8)
% 17.58/17.77          | ~ (v1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77          | (v2_struct_0 @ (k2_tsep_1 @ X8 @ X7 @ X9))
% 17.58/17.77          | (r1_tsep_1 @ X7 @ X9)
% 17.58/17.77          | ~ (m1_pre_topc @ X7 @ X8)
% 17.58/17.77          | (v2_struct_0 @ X7))),
% 17.58/17.77      inference('simplify', [status(thm)], ['26'])).
% 17.58/17.77  thf('79', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | ~ (l1_pre_topc @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_A))),
% 17.58/17.77      inference('sup-', [status(thm)], ['77', '78'])).
% 17.58/17.77  thf('80', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('83', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A))),
% 17.58/17.77      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 17.58/17.77  thf('84', plain,
% 17.58/17.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['83'])).
% 17.58/17.77  thf('85', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 17.58/17.77      inference('sup-', [status(thm)], ['76', '84'])).
% 17.58/17.77  thf('86', plain,
% 17.58/17.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['85'])).
% 17.58/17.77  thf('87', plain,
% 17.58/17.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X11 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X11)
% 17.58/17.77          | ~ (l1_pre_topc @ X12)
% 17.58/17.77          | (v2_struct_0 @ X12)
% 17.58/17.77          | (v2_struct_0 @ X13)
% 17.58/17.77          | ~ (m1_pre_topc @ X13 @ X12)
% 17.58/17.77          | ~ (v2_struct_0 @ (k2_tsep_1 @ X12 @ X11 @ X13)))),
% 17.58/17.77      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 17.58/17.77  thf('88', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | ~ (l1_pre_topc @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 17.58/17.77      inference('sup-', [status(thm)], ['86', '87'])).
% 17.58/17.77  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('91', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('92', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 17.58/17.77  thf('93', plain,
% 17.58/17.77      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 17.58/17.77          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['92'])).
% 17.58/17.77  thf('94', plain,
% 17.58/17.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.58/17.77         (~ (m1_pre_topc @ X14 @ X15)
% 17.58/17.77          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 17.58/17.77          | (m1_pre_topc @ X14 @ X16)
% 17.58/17.77          | ~ (m1_pre_topc @ X16 @ X15)
% 17.58/17.77          | ~ (l1_pre_topc @ X15)
% 17.58/17.77          | ~ (v2_pre_topc @ X15))),
% 17.58/17.77      inference('cnf', [status(esa)], [t4_tsep_1])).
% 17.58/17.77  thf('95', plain,
% 17.58/17.77      (![X0 : $i, X1 : $i]:
% 17.58/17.77         (~ (r1_tarski @ 
% 17.58/17.77             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 17.58/17.77             (u1_struct_0 @ X0))
% 17.58/17.77          | (v2_struct_0 @ sk_C)
% 17.58/17.77          | (v2_struct_0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ sk_B)
% 17.58/17.77          | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77          | ~ (v2_pre_topc @ X1)
% 17.58/17.77          | ~ (l1_pre_topc @ X1)
% 17.58/17.77          | ~ (m1_pre_topc @ X0 @ X1)
% 17.58/17.77          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 17.58/17.77      inference('sup-', [status(thm)], ['93', '94'])).
% 17.58/17.77  thf('96', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v2_struct_0 @ sk_C)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_B)
% 17.58/17.77          | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 17.58/17.77          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 17.58/17.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 17.58/17.77          | ~ (l1_pre_topc @ X0)
% 17.58/17.77          | ~ (v2_pre_topc @ X0)
% 17.58/17.77          | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77          | (v2_struct_0 @ sk_B)
% 17.58/17.77          | (v2_struct_0 @ sk_A)
% 17.58/17.77          | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('sup-', [status(thm)], ['69', '95'])).
% 17.58/17.77  thf('97', plain,
% 17.58/17.77      (![X0 : $i]:
% 17.58/17.77         ((v2_struct_0 @ sk_A)
% 17.58/17.77          | ~ (v2_pre_topc @ X0)
% 17.58/17.77          | ~ (l1_pre_topc @ X0)
% 17.58/17.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 17.58/17.77          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 17.58/17.77          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 17.58/17.77          | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77          | (v2_struct_0 @ sk_B)
% 17.58/17.77          | (v2_struct_0 @ sk_D)
% 17.58/17.77          | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['96'])).
% 17.58/17.77  thf('98', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 17.58/17.77        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 17.58/17.77        | ~ (l1_pre_topc @ sk_A)
% 17.58/17.77        | ~ (v2_pre_topc @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_A))),
% 17.58/17.77      inference('sup-', [status(thm)], ['7', '97'])).
% 17.58/17.77  thf('99', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('102', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_A))),
% 17.58/17.77      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 17.58/17.77  thf('103', plain,
% 17.58/17.77      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('simplify', [status(thm)], ['102'])).
% 17.58/17.77  thf('104', plain,
% 17.58/17.77      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('105', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_D)
% 17.58/17.77        | (r1_tsep_1 @ sk_B @ sk_C))),
% 17.58/17.77      inference('sup-', [status(thm)], ['103', '104'])).
% 17.58/17.77  thf('106', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('107', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_D)
% 17.58/17.77        | (v2_struct_0 @ sk_B)
% 17.58/17.77        | (v2_struct_0 @ sk_A)
% 17.58/17.77        | (v2_struct_0 @ sk_C))),
% 17.58/17.77      inference('sup-', [status(thm)], ['105', '106'])).
% 17.58/17.77  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('109', plain,
% 17.58/17.77      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 17.58/17.77      inference('sup-', [status(thm)], ['107', '108'])).
% 17.58/17.77  thf('110', plain, (~ (v2_struct_0 @ sk_C)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('111', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 17.58/17.77      inference('clc', [status(thm)], ['109', '110'])).
% 17.58/17.77  thf('112', plain, (~ (v2_struct_0 @ sk_D)),
% 17.58/17.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.58/17.77  thf('113', plain, ((v2_struct_0 @ sk_B)),
% 17.58/17.77      inference('clc', [status(thm)], ['111', '112'])).
% 17.58/17.77  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 17.58/17.77  
% 17.58/17.77  % SZS output end Refutation
% 17.58/17.77  
% 17.58/17.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
