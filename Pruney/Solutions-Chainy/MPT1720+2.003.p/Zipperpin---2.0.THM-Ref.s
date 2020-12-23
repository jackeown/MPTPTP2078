%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2wW8zQdowy

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:28 EST 2020

% Result     : Theorem 23.14s
% Output     : Refutation 23.14s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 348 expanded)
%              Number of leaves         :   24 ( 105 expanded)
%              Depth                    :   26
%              Number of atoms          : 1809 (6702 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
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

thf('27',plain,(
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
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

thf('57',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_pre_topc @ X13 @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( k1_tsep_1 @ X17 @ X16 @ X16 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ( m1_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['55','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('96',plain,(
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
    inference(simplify,[status(thm)],['26'])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
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
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('106',plain,
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
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['110'])).

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
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['87','113'])).

thf('115',plain,(
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
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
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
    inference('sup-',[status(thm)],['7','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
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
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2wW8zQdowy
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:02:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 23.14/23.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 23.14/23.34  % Solved by: fo/fo7.sh
% 23.14/23.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.14/23.34  % done 8584 iterations in 22.893s
% 23.14/23.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 23.14/23.34  % SZS output start Refutation
% 23.14/23.34  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 23.14/23.34  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 23.14/23.34  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 23.14/23.34  thf(sk_B_type, type, sk_B: $i).
% 23.14/23.34  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 23.14/23.34  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 23.14/23.34  thf(sk_A_type, type, sk_A: $i).
% 23.14/23.34  thf(sk_D_type, type, sk_D: $i).
% 23.14/23.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 23.14/23.34  thf(sk_C_type, type, sk_C: $i).
% 23.14/23.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 23.14/23.34  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 23.14/23.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 23.14/23.34  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 23.14/23.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 23.14/23.34  thf(t29_tmap_1, conjecture,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.14/23.34       ( ![B:$i]:
% 23.14/23.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 23.14/23.34           ( ![C:$i]:
% 23.14/23.34             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 23.14/23.34               ( ![D:$i]:
% 23.14/23.34                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 23.14/23.34                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 23.14/23.34                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 23.14/23.34  thf(zf_stmt_0, negated_conjecture,
% 23.14/23.34    (~( ![A:$i]:
% 23.14/23.34        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 23.14/23.34            ( l1_pre_topc @ A ) ) =>
% 23.14/23.34          ( ![B:$i]:
% 23.14/23.34            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 23.14/23.34              ( ![C:$i]:
% 23.14/23.34                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 23.14/23.34                  ( ![D:$i]:
% 23.14/23.34                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 23.14/23.34                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 23.14/23.34                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 23.14/23.34    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 23.14/23.34  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf(dt_k1_tsep_1, axiom,
% 23.14/23.34    (![A:$i,B:$i,C:$i]:
% 23.14/23.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 23.14/23.34         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 23.14/23.34         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 23.14/23.34       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 23.14/23.34         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 23.14/23.34         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 23.14/23.34  thf('3', plain,
% 23.14/23.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X10 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X10)
% 23.14/23.34          | ~ (l1_pre_topc @ X11)
% 23.14/23.34          | (v2_struct_0 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X12)
% 23.14/23.34          | ~ (m1_pre_topc @ X12 @ X11)
% 23.14/23.34          | (m1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12) @ X11))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 23.14/23.34  thf('4', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_A)
% 23.14/23.34          | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('sup-', [status(thm)], ['2', '3'])).
% 23.14/23.34  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('6', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('demod', [status(thm)], ['4', '5'])).
% 23.14/23.34  thf('7', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 23.14/23.34      inference('sup-', [status(thm)], ['1', '6'])).
% 23.14/23.34  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('10', plain,
% 23.14/23.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X10 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X10)
% 23.14/23.34          | ~ (l1_pre_topc @ X11)
% 23.14/23.34          | (v2_struct_0 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X12)
% 23.14/23.34          | ~ (m1_pre_topc @ X12 @ X11)
% 23.14/23.34          | (v1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 23.14/23.34  thf('11', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | ~ (l1_pre_topc @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('sup-', [status(thm)], ['9', '10'])).
% 23.14/23.34  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf(dt_m1_pre_topc, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( l1_pre_topc @ A ) =>
% 23.14/23.34       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 23.14/23.34  thf('13', plain,
% 23.14/23.34      (![X2 : $i, X3 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 23.14/23.34  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['12', '13'])).
% 23.14/23.34  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['14', '15'])).
% 23.14/23.34  thf('17', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('demod', [status(thm)], ['11', '16'])).
% 23.14/23.34  thf('18', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)))),
% 23.14/23.34      inference('sup-', [status(thm)], ['8', '17'])).
% 23.14/23.34  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('21', plain,
% 23.14/23.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X10 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X10)
% 23.14/23.34          | ~ (l1_pre_topc @ X11)
% 23.14/23.34          | (v2_struct_0 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X12)
% 23.14/23.34          | ~ (m1_pre_topc @ X12 @ X11)
% 23.14/23.34          | (m1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12) @ X11))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 23.14/23.34  thf('22', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | ~ (l1_pre_topc @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('sup-', [status(thm)], ['20', '21'])).
% 23.14/23.34  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['14', '15'])).
% 23.14/23.34  thf('24', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('demod', [status(thm)], ['22', '23'])).
% 23.14/23.34  thf('25', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['19', '24'])).
% 23.14/23.34  thf(d2_tsep_1, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 23.14/23.34       ( ![B:$i]:
% 23.14/23.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 23.14/23.34           ( ![C:$i]:
% 23.14/23.34             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 23.14/23.34               ( ![D:$i]:
% 23.14/23.34                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 23.14/23.34                     ( m1_pre_topc @ D @ A ) ) =>
% 23.14/23.34                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 23.14/23.34                     ( ( u1_struct_0 @ D ) =
% 23.14/23.34                       ( k2_xboole_0 @
% 23.14/23.34                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 23.14/23.34  thf('26', plain,
% 23.14/23.34      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 23.14/23.34         ((v2_struct_0 @ X6)
% 23.14/23.34          | ~ (m1_pre_topc @ X6 @ X7)
% 23.14/23.34          | (v2_struct_0 @ X8)
% 23.14/23.34          | ~ (v1_pre_topc @ X8)
% 23.14/23.34          | ~ (m1_pre_topc @ X8 @ X7)
% 23.14/23.34          | ((X8) != (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34          | ((u1_struct_0 @ X8)
% 23.14/23.34              = (k2_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X9)))
% 23.14/23.34          | ~ (m1_pre_topc @ X9 @ X7)
% 23.14/23.34          | (v2_struct_0 @ X9)
% 23.14/23.34          | ~ (l1_pre_topc @ X7)
% 23.14/23.34          | (v2_struct_0 @ X7))),
% 23.14/23.34      inference('cnf', [status(esa)], [d2_tsep_1])).
% 23.14/23.34  thf('27', plain,
% 23.14/23.34      (![X6 : $i, X7 : $i, X9 : $i]:
% 23.14/23.34         ((v2_struct_0 @ X7)
% 23.14/23.34          | ~ (l1_pre_topc @ X7)
% 23.14/23.34          | (v2_struct_0 @ X9)
% 23.14/23.34          | ~ (m1_pre_topc @ X9 @ X7)
% 23.14/23.34          | ((u1_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34              = (k2_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X9)))
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9) @ X7)
% 23.14/23.34          | ~ (v1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34          | (v2_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34          | ~ (m1_pre_topc @ X6 @ X7)
% 23.14/23.34          | (v2_struct_0 @ X6))),
% 23.14/23.34      inference('simplify', [status(thm)], ['26'])).
% 23.14/23.34  thf('28', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | ~ (l1_pre_topc @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['25', '27'])).
% 23.14/23.34  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['14', '15'])).
% 23.14/23.34  thf('32', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 23.14/23.34  thf('33', plain,
% 23.14/23.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['32'])).
% 23.14/23.34  thf('34', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 23.14/23.34      inference('sup-', [status(thm)], ['18', '33'])).
% 23.14/23.34  thf('35', plain,
% 23.14/23.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['34'])).
% 23.14/23.34  thf('36', plain,
% 23.14/23.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X10 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X10)
% 23.14/23.34          | ~ (l1_pre_topc @ X11)
% 23.14/23.34          | (v2_struct_0 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X12)
% 23.14/23.34          | ~ (m1_pre_topc @ X12 @ X11)
% 23.14/23.34          | ~ (v2_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 23.14/23.34  thf('37', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | ~ (l1_pre_topc @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ~ (m1_pre_topc @ sk_B @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['35', '36'])).
% 23.14/23.34  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['14', '15'])).
% 23.14/23.34  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('41', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 23.14/23.34  thf('42', plain,
% 23.14/23.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 23.14/23.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['41'])).
% 23.14/23.34  thf('43', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['19', '24'])).
% 23.14/23.34  thf('44', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['19', '24'])).
% 23.14/23.34  thf(t4_tsep_1, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.14/23.34       ( ![B:$i]:
% 23.14/23.34         ( ( m1_pre_topc @ B @ A ) =>
% 23.14/23.34           ( ![C:$i]:
% 23.14/23.34             ( ( m1_pre_topc @ C @ A ) =>
% 23.14/23.34               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 23.14/23.34                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 23.14/23.34  thf('45', plain,
% 23.14/23.34      (![X18 : $i, X19 : $i, X20 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X18 @ X19)
% 23.14/23.34          | ~ (m1_pre_topc @ X18 @ X20)
% 23.14/23.34          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 23.14/23.34          | ~ (m1_pre_topc @ X20 @ X19)
% 23.14/23.34          | ~ (l1_pre_topc @ X19)
% 23.14/23.34          | ~ (v2_pre_topc @ X19))),
% 23.14/23.34      inference('cnf', [status(esa)], [t4_tsep_1])).
% 23.14/23.34  thf('46', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v2_struct_0 @ sk_D)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B)
% 23.14/23.34          | ~ (v2_pre_topc @ sk_C)
% 23.14/23.34          | ~ (l1_pre_topc @ sk_C)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 23.14/23.34          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 23.14/23.34             (u1_struct_0 @ X0))
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ X0))),
% 23.14/23.34      inference('sup-', [status(thm)], ['44', '45'])).
% 23.14/23.34  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf(cc1_pre_topc, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.14/23.34       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 23.14/23.34  thf('48', plain,
% 23.14/23.34      (![X0 : $i, X1 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X0 @ X1)
% 23.14/23.34          | (v2_pre_topc @ X0)
% 23.14/23.34          | ~ (l1_pre_topc @ X1)
% 23.14/23.34          | ~ (v2_pre_topc @ X1))),
% 23.14/23.34      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 23.14/23.34  thf('49', plain,
% 23.14/23.34      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['47', '48'])).
% 23.14/23.34  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('52', plain, ((v2_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['49', '50', '51'])).
% 23.14/23.34  thf('53', plain, ((l1_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['14', '15'])).
% 23.14/23.34  thf('54', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v2_struct_0 @ sk_D)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 23.14/23.34          | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 23.14/23.34             (u1_struct_0 @ X0))
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ X0))),
% 23.14/23.34      inference('demod', [status(thm)], ['46', '52', '53'])).
% 23.14/23.34  thf('55', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 23.14/23.34           (u1_struct_0 @ sk_C))
% 23.14/23.34        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('sup-', [status(thm)], ['43', '54'])).
% 23.14/23.34  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('57', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf(t22_tsep_1, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.14/23.34       ( ![B:$i]:
% 23.14/23.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 23.14/23.34           ( ![C:$i]:
% 23.14/23.34             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 23.14/23.34               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 23.14/23.34  thf('58', plain,
% 23.14/23.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 23.14/23.34         ((v2_struct_0 @ X13)
% 23.14/23.34          | ~ (m1_pre_topc @ X13 @ X14)
% 23.14/23.34          | (m1_pre_topc @ X13 @ (k1_tsep_1 @ X14 @ X13 @ X15))
% 23.14/23.34          | ~ (m1_pre_topc @ X15 @ X14)
% 23.14/23.34          | (v2_struct_0 @ X15)
% 23.14/23.34          | ~ (l1_pre_topc @ X14)
% 23.14/23.34          | ~ (v2_pre_topc @ X14)
% 23.14/23.34          | (v2_struct_0 @ X14))),
% 23.14/23.34      inference('cnf', [status(esa)], [t22_tsep_1])).
% 23.14/23.34  thf('59', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v2_struct_0 @ sk_A)
% 23.14/23.34          | ~ (v2_pre_topc @ sk_A)
% 23.14/23.34          | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 23.14/23.34          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 23.14/23.34          | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['57', '58'])).
% 23.14/23.34  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('62', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v2_struct_0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 23.14/23.34          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 23.14/23.34          | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('demod', [status(thm)], ['59', '60', '61'])).
% 23.14/23.34  thf('63', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_C)
% 23.14/23.34        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_A))),
% 23.14/23.34      inference('sup-', [status(thm)], ['56', '62'])).
% 23.14/23.34  thf('64', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_A)
% 23.14/23.34        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 23.14/23.34        | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('simplify', [status(thm)], ['63'])).
% 23.14/23.34  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('66', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_C)
% 23.14/23.34        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 23.14/23.34      inference('clc', [status(thm)], ['64', '65'])).
% 23.14/23.34  thf('67', plain, (~ (v2_struct_0 @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('68', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 23.14/23.34      inference('clc', [status(thm)], ['66', '67'])).
% 23.14/23.34  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf(t25_tmap_1, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.14/23.34       ( ![B:$i]:
% 23.14/23.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 23.14/23.34           ( ( k1_tsep_1 @ A @ B @ B ) =
% 23.14/23.34             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 23.14/23.34  thf('70', plain,
% 23.14/23.34      (![X16 : $i, X17 : $i]:
% 23.14/23.34         ((v2_struct_0 @ X16)
% 23.14/23.34          | ~ (m1_pre_topc @ X16 @ X17)
% 23.14/23.34          | ((k1_tsep_1 @ X17 @ X16 @ X16)
% 23.14/23.34              = (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 23.14/23.34          | ~ (l1_pre_topc @ X17)
% 23.14/23.34          | ~ (v2_pre_topc @ X17)
% 23.14/23.34          | (v2_struct_0 @ X17))),
% 23.14/23.34      inference('cnf', [status(esa)], [t25_tmap_1])).
% 23.14/23.34  thf('71', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_A)
% 23.14/23.34        | ~ (v2_pre_topc @ sk_A)
% 23.14/23.34        | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 23.14/23.34            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 23.14/23.34        | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['69', '70'])).
% 23.14/23.34  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('74', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_A)
% 23.14/23.34        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 23.14/23.34            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 23.14/23.34        | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('demod', [status(thm)], ['71', '72', '73'])).
% 23.14/23.34  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('76', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_C)
% 23.14/23.34        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 23.14/23.34            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 23.14/23.34      inference('clc', [status(thm)], ['74', '75'])).
% 23.14/23.34  thf('77', plain, (~ (v2_struct_0 @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('78', plain,
% 23.14/23.34      (((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 23.14/23.34         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 23.14/23.34      inference('clc', [status(thm)], ['76', '77'])).
% 23.14/23.34  thf(t59_pre_topc, axiom,
% 23.14/23.34    (![A:$i]:
% 23.14/23.34     ( ( l1_pre_topc @ A ) =>
% 23.14/23.34       ( ![B:$i]:
% 23.14/23.34         ( ( m1_pre_topc @
% 23.14/23.34             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 23.14/23.34           ( m1_pre_topc @ B @ A ) ) ) ))).
% 23.14/23.34  thf('79', plain,
% 23.14/23.34      (![X4 : $i, X5 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X4 @ 
% 23.14/23.34             (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 23.14/23.34          | (m1_pre_topc @ X4 @ X5)
% 23.14/23.34          | ~ (l1_pre_topc @ X5))),
% 23.14/23.34      inference('cnf', [status(esa)], [t59_pre_topc])).
% 23.14/23.34  thf('80', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 23.14/23.34          | ~ (l1_pre_topc @ sk_C)
% 23.14/23.34          | (m1_pre_topc @ X0 @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['78', '79'])).
% 23.14/23.34  thf('81', plain, ((l1_pre_topc @ sk_C)),
% 23.14/23.34      inference('demod', [status(thm)], ['14', '15'])).
% 23.14/23.34  thf('82', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 23.14/23.34          | (m1_pre_topc @ X0 @ sk_C))),
% 23.14/23.34      inference('demod', [status(thm)], ['80', '81'])).
% 23.14/23.34  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 23.14/23.34      inference('sup-', [status(thm)], ['68', '82'])).
% 23.14/23.34  thf('84', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 23.14/23.34           (u1_struct_0 @ sk_C))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('demod', [status(thm)], ['55', '83'])).
% 23.14/23.34  thf('85', plain,
% 23.14/23.34      (((r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 23.14/23.34         (u1_struct_0 @ sk_C))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['84'])).
% 23.14/23.34  thf('86', plain,
% 23.14/23.34      (((r1_tarski @ 
% 23.14/23.34         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 23.14/23.34         (u1_struct_0 @ sk_C))
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('sup+', [status(thm)], ['42', '85'])).
% 23.14/23.34  thf('87', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (r1_tarski @ 
% 23.14/23.34           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 23.14/23.34           (u1_struct_0 @ sk_C)))),
% 23.14/23.34      inference('simplify', [status(thm)], ['86'])).
% 23.14/23.34  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('90', plain,
% 23.14/23.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X10 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X10)
% 23.14/23.34          | ~ (l1_pre_topc @ X11)
% 23.14/23.34          | (v2_struct_0 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X12)
% 23.14/23.34          | ~ (m1_pre_topc @ X12 @ X11)
% 23.14/23.34          | (v1_pre_topc @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 23.14/23.34  thf('91', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_A)
% 23.14/23.34          | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('sup-', [status(thm)], ['89', '90'])).
% 23.14/23.34  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('93', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('demod', [status(thm)], ['91', '92'])).
% 23.14/23.34  thf('94', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 23.14/23.34      inference('sup-', [status(thm)], ['88', '93'])).
% 23.14/23.34  thf('95', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 23.14/23.34      inference('sup-', [status(thm)], ['1', '6'])).
% 23.14/23.34  thf('96', plain,
% 23.14/23.34      (![X6 : $i, X7 : $i, X9 : $i]:
% 23.14/23.34         ((v2_struct_0 @ X7)
% 23.14/23.34          | ~ (l1_pre_topc @ X7)
% 23.14/23.34          | (v2_struct_0 @ X9)
% 23.14/23.34          | ~ (m1_pre_topc @ X9 @ X7)
% 23.14/23.34          | ((u1_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34              = (k2_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X9)))
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9) @ X7)
% 23.14/23.34          | ~ (v1_pre_topc @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34          | (v2_struct_0 @ (k1_tsep_1 @ X7 @ X6 @ X9))
% 23.14/23.34          | ~ (m1_pre_topc @ X6 @ X7)
% 23.14/23.34          | (v2_struct_0 @ X6))),
% 23.14/23.34      inference('simplify', [status(thm)], ['26'])).
% 23.14/23.34  thf('97', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_A))),
% 23.14/23.34      inference('sup-', [status(thm)], ['95', '96'])).
% 23.14/23.34  thf('98', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('99', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('101', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A))),
% 23.14/23.34      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 23.14/23.34  thf('102', plain,
% 23.14/23.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['101'])).
% 23.14/23.34  thf('103', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 23.14/23.34      inference('sup-', [status(thm)], ['94', '102'])).
% 23.14/23.34  thf('104', plain,
% 23.14/23.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['103'])).
% 23.14/23.34  thf('105', plain,
% 23.14/23.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X10 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X10)
% 23.14/23.34          | ~ (l1_pre_topc @ X11)
% 23.14/23.34          | (v2_struct_0 @ X11)
% 23.14/23.34          | (v2_struct_0 @ X12)
% 23.14/23.34          | ~ (m1_pre_topc @ X12 @ X11)
% 23.14/23.34          | ~ (v2_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)))),
% 23.14/23.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 23.14/23.34  thf('106', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 23.14/23.34      inference('sup-', [status(thm)], ['104', '105'])).
% 23.14/23.34  thf('107', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('109', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('110', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 23.14/23.34  thf('111', plain,
% 23.14/23.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 23.14/23.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['110'])).
% 23.14/23.34  thf('112', plain,
% 23.14/23.34      (![X18 : $i, X19 : $i, X20 : $i]:
% 23.14/23.34         (~ (m1_pre_topc @ X18 @ X19)
% 23.14/23.34          | ~ (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 23.14/23.34          | (m1_pre_topc @ X18 @ X20)
% 23.14/23.34          | ~ (m1_pre_topc @ X20 @ X19)
% 23.14/23.34          | ~ (l1_pre_topc @ X19)
% 23.14/23.34          | ~ (v2_pre_topc @ X19))),
% 23.14/23.34      inference('cnf', [status(esa)], [t4_tsep_1])).
% 23.14/23.34  thf('113', plain,
% 23.14/23.34      (![X0 : $i, X1 : $i]:
% 23.14/23.34         (~ (r1_tarski @ 
% 23.14/23.34             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 23.14/23.34             (u1_struct_0 @ X0))
% 23.14/23.34          | (v2_struct_0 @ sk_D)
% 23.14/23.34          | (v2_struct_0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ sk_B)
% 23.14/23.34          | ~ (v2_pre_topc @ X1)
% 23.14/23.34          | ~ (l1_pre_topc @ X1)
% 23.14/23.34          | ~ (m1_pre_topc @ X0 @ X1)
% 23.14/23.34          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X1))),
% 23.14/23.34      inference('sup-', [status(thm)], ['111', '112'])).
% 23.14/23.34  thf('114', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v2_struct_0 @ sk_D)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_B)
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 23.14/23.34          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 23.14/23.34          | ~ (m1_pre_topc @ sk_C @ X0)
% 23.14/23.34          | ~ (l1_pre_topc @ X0)
% 23.14/23.34          | ~ (v2_pre_topc @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_B)
% 23.14/23.34          | (v2_struct_0 @ sk_A)
% 23.14/23.34          | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('sup-', [status(thm)], ['87', '113'])).
% 23.14/23.34  thf('115', plain,
% 23.14/23.34      (![X0 : $i]:
% 23.14/23.34         ((v2_struct_0 @ sk_A)
% 23.14/23.34          | ~ (v2_pre_topc @ X0)
% 23.14/23.34          | ~ (l1_pre_topc @ X0)
% 23.14/23.34          | ~ (m1_pre_topc @ sk_C @ X0)
% 23.14/23.34          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 23.14/23.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 23.14/23.34          | (v2_struct_0 @ sk_B)
% 23.14/23.34          | (v2_struct_0 @ sk_C)
% 23.14/23.34          | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['114'])).
% 23.14/23.34  thf('116', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 23.14/23.34        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 23.14/23.34        | ~ (l1_pre_topc @ sk_A)
% 23.14/23.34        | ~ (v2_pre_topc @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_A))),
% 23.14/23.34      inference('sup-', [status(thm)], ['7', '115'])).
% 23.14/23.34  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('120', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_A))),
% 23.14/23.34      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 23.14/23.34  thf('121', plain,
% 23.14/23.34      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_C)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('simplify', [status(thm)], ['120'])).
% 23.14/23.34  thf('122', plain,
% 23.14/23.34      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('123', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_D)
% 23.14/23.34        | (v2_struct_0 @ sk_A)
% 23.14/23.34        | (v2_struct_0 @ sk_B)
% 23.14/23.34        | (v2_struct_0 @ sk_C))),
% 23.14/23.34      inference('sup-', [status(thm)], ['121', '122'])).
% 23.14/23.34  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('125', plain,
% 23.14/23.34      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 23.14/23.34      inference('sup-', [status(thm)], ['123', '124'])).
% 23.14/23.34  thf('126', plain, (~ (v2_struct_0 @ sk_C)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('127', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 23.14/23.34      inference('clc', [status(thm)], ['125', '126'])).
% 23.14/23.34  thf('128', plain, (~ (v2_struct_0 @ sk_D)),
% 23.14/23.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.14/23.34  thf('129', plain, ((v2_struct_0 @ sk_B)),
% 23.14/23.34      inference('clc', [status(thm)], ['127', '128'])).
% 23.14/23.34  thf('130', plain, ($false), inference('demod', [status(thm)], ['0', '129'])).
% 23.14/23.34  
% 23.14/23.34  % SZS output end Refutation
% 23.14/23.34  
% 23.14/23.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
