%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dAvS6SH5z

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:30 EST 2020

% Result     : Theorem 35.21s
% Output     : Refutation 35.21s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 354 expanded)
%              Number of leaves         :   26 ( 108 expanded)
%              Depth                    :   27
%              Number of atoms          : 1916 (7271 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( r1_tsep_1 @ X6 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( v1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ( X9
       != ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
      | ( ( u1_struct_0 @ X9 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) @ X7 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
      | ( r1_tsep_1 @ X6 @ X8 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
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

thf('57',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
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
      | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
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
      | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
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
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
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
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','85'])).

thf('87',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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
      | ( v1_pre_topc @ ( k2_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
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
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('96',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) @ X7 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X7 @ X6 @ X8 ) )
      | ( r1_tsep_1 @ X6 @ X8 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
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
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
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
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('106',plain,
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
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
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
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['87','113'])).

thf('115',plain,(
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
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
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
    inference('sup-',[status(thm)],['7','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4dAvS6SH5z
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 35.21/35.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 35.21/35.40  % Solved by: fo/fo7.sh
% 35.21/35.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.21/35.40  % done 14874 iterations in 34.942s
% 35.21/35.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 35.21/35.40  % SZS output start Refutation
% 35.21/35.40  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 35.21/35.40  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 35.21/35.40  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 35.21/35.40  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 35.21/35.40  thf(sk_D_type, type, sk_D: $i).
% 35.21/35.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 35.21/35.40  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 35.21/35.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 35.21/35.40  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 35.21/35.40  thf(sk_A_type, type, sk_A: $i).
% 35.21/35.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 35.21/35.40  thf(sk_B_type, type, sk_B: $i).
% 35.21/35.40  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 35.21/35.40  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 35.21/35.40  thf(sk_C_type, type, sk_C: $i).
% 35.21/35.40  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 35.21/35.40  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 35.21/35.40  thf(t30_tmap_1, conjecture,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.21/35.40       ( ![B:$i]:
% 35.21/35.40         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 35.21/35.40           ( ![C:$i]:
% 35.21/35.40             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 35.21/35.40               ( ![D:$i]:
% 35.21/35.40                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 35.21/35.40                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 35.21/35.40                     ( ( r1_tsep_1 @ B @ C ) | 
% 35.21/35.40                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 35.21/35.40  thf(zf_stmt_0, negated_conjecture,
% 35.21/35.40    (~( ![A:$i]:
% 35.21/35.40        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 35.21/35.40            ( l1_pre_topc @ A ) ) =>
% 35.21/35.40          ( ![B:$i]:
% 35.21/35.40            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 35.21/35.40              ( ![C:$i]:
% 35.21/35.40                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 35.21/35.40                  ( ![D:$i]:
% 35.21/35.40                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 35.21/35.40                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 35.21/35.40                        ( ( r1_tsep_1 @ B @ C ) | 
% 35.21/35.40                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 35.21/35.40    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 35.21/35.40  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf(dt_k2_tsep_1, axiom,
% 35.21/35.40    (![A:$i,B:$i,C:$i]:
% 35.21/35.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 35.21/35.40         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 35.21/35.40         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 35.21/35.40       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 35.21/35.40         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 35.21/35.40         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 35.21/35.40  thf('3', plain,
% 35.21/35.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X10 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X10)
% 35.21/35.40          | ~ (l1_pre_topc @ X11)
% 35.21/35.40          | (v2_struct_0 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X12)
% 35.21/35.40          | ~ (m1_pre_topc @ X12 @ X11)
% 35.21/35.40          | (m1_pre_topc @ (k2_tsep_1 @ X11 @ X10 @ X12) @ X11))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 35.21/35.40  thf('4', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_A)
% 35.21/35.40          | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('sup-', [status(thm)], ['2', '3'])).
% 35.21/35.40  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('6', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('demod', [status(thm)], ['4', '5'])).
% 35.21/35.40  thf('7', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 35.21/35.40      inference('sup-', [status(thm)], ['1', '6'])).
% 35.21/35.40  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('10', plain,
% 35.21/35.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X10 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X10)
% 35.21/35.40          | ~ (l1_pre_topc @ X11)
% 35.21/35.40          | (v2_struct_0 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X12)
% 35.21/35.40          | ~ (m1_pre_topc @ X12 @ X11)
% 35.21/35.40          | (v1_pre_topc @ (k2_tsep_1 @ X11 @ X10 @ X12)))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 35.21/35.40  thf('11', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0))
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | ~ (l1_pre_topc @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('sup-', [status(thm)], ['9', '10'])).
% 35.21/35.40  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf(dt_m1_pre_topc, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( l1_pre_topc @ A ) =>
% 35.21/35.40       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 35.21/35.40  thf('13', plain,
% 35.21/35.40      (![X2 : $i, X3 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 35.21/35.40  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['12', '13'])).
% 35.21/35.40  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['14', '15'])).
% 35.21/35.40  thf('17', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0))
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('demod', [status(thm)], ['11', '16'])).
% 35.21/35.40  thf('18', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)))),
% 35.21/35.40      inference('sup-', [status(thm)], ['8', '17'])).
% 35.21/35.40  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('21', plain,
% 35.21/35.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X10 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X10)
% 35.21/35.40          | ~ (l1_pre_topc @ X11)
% 35.21/35.40          | (v2_struct_0 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X12)
% 35.21/35.40          | ~ (m1_pre_topc @ X12 @ X11)
% 35.21/35.40          | (m1_pre_topc @ (k2_tsep_1 @ X11 @ X10 @ X12) @ X11))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 35.21/35.40  thf('22', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0) @ sk_D)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | ~ (l1_pre_topc @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('sup-', [status(thm)], ['20', '21'])).
% 35.21/35.40  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['14', '15'])).
% 35.21/35.40  thf('24', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0) @ sk_D)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('demod', [status(thm)], ['22', '23'])).
% 35.21/35.40  thf('25', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['19', '24'])).
% 35.21/35.40  thf(d5_tsep_1, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 35.21/35.40       ( ![B:$i]:
% 35.21/35.40         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 35.21/35.40           ( ![C:$i]:
% 35.21/35.40             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 35.21/35.40               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 35.21/35.40                 ( ![D:$i]:
% 35.21/35.40                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 35.21/35.40                       ( m1_pre_topc @ D @ A ) ) =>
% 35.21/35.40                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 35.21/35.40                       ( ( u1_struct_0 @ D ) =
% 35.21/35.40                         ( k3_xboole_0 @
% 35.21/35.40                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 35.21/35.40  thf('26', plain,
% 35.21/35.40      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 35.21/35.40         ((v2_struct_0 @ X6)
% 35.21/35.40          | ~ (m1_pre_topc @ X6 @ X7)
% 35.21/35.40          | (r1_tsep_1 @ X6 @ X8)
% 35.21/35.40          | (v2_struct_0 @ X9)
% 35.21/35.40          | ~ (v1_pre_topc @ X9)
% 35.21/35.40          | ~ (m1_pre_topc @ X9 @ X7)
% 35.21/35.40          | ((X9) != (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40          | ((u1_struct_0 @ X9)
% 35.21/35.40              = (k3_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X8)))
% 35.21/35.40          | ~ (m1_pre_topc @ X8 @ X7)
% 35.21/35.40          | (v2_struct_0 @ X8)
% 35.21/35.40          | ~ (l1_pre_topc @ X7)
% 35.21/35.40          | (v2_struct_0 @ X7))),
% 35.21/35.40      inference('cnf', [status(esa)], [d5_tsep_1])).
% 35.21/35.40  thf('27', plain,
% 35.21/35.40      (![X6 : $i, X7 : $i, X8 : $i]:
% 35.21/35.40         ((v2_struct_0 @ X7)
% 35.21/35.40          | ~ (l1_pre_topc @ X7)
% 35.21/35.40          | (v2_struct_0 @ X8)
% 35.21/35.40          | ~ (m1_pre_topc @ X8 @ X7)
% 35.21/35.40          | ((u1_struct_0 @ (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40              = (k3_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X8)))
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ X7 @ X6 @ X8) @ X7)
% 35.21/35.40          | ~ (v1_pre_topc @ (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40          | (v2_struct_0 @ (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40          | (r1_tsep_1 @ X6 @ X8)
% 35.21/35.40          | ~ (m1_pre_topc @ X6 @ X7)
% 35.21/35.40          | (v2_struct_0 @ X6))),
% 35.21/35.40      inference('simplify', [status(thm)], ['26'])).
% 35.21/35.40  thf('28', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | ~ (m1_pre_topc @ sk_B @ sk_D)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | ~ (l1_pre_topc @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['25', '27'])).
% 35.21/35.40  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['14', '15'])).
% 35.21/35.40  thf('32', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 35.21/35.40  thf('33', plain,
% 35.21/35.40      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['32'])).
% 35.21/35.40  thf('34', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 35.21/35.40      inference('sup-', [status(thm)], ['18', '33'])).
% 35.21/35.40  thf('35', plain,
% 35.21/35.40      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['34'])).
% 35.21/35.40  thf('36', plain,
% 35.21/35.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X10 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X10)
% 35.21/35.40          | ~ (l1_pre_topc @ X11)
% 35.21/35.40          | (v2_struct_0 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X12)
% 35.21/35.40          | ~ (m1_pre_topc @ X12 @ X11)
% 35.21/35.40          | ~ (v2_struct_0 @ (k2_tsep_1 @ X11 @ X10 @ X12)))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 35.21/35.40  thf('37', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | ~ (l1_pre_topc @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | ~ (m1_pre_topc @ sk_B @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['35', '36'])).
% 35.21/35.40  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['14', '15'])).
% 35.21/35.40  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('41', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 35.21/35.40  thf('42', plain,
% 35.21/35.40      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 35.21/35.40          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['41'])).
% 35.21/35.40  thf('43', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['19', '24'])).
% 35.21/35.40  thf('44', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['19', '24'])).
% 35.21/35.40  thf(t4_tsep_1, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.21/35.40       ( ![B:$i]:
% 35.21/35.40         ( ( m1_pre_topc @ B @ A ) =>
% 35.21/35.40           ( ![C:$i]:
% 35.21/35.40             ( ( m1_pre_topc @ C @ A ) =>
% 35.21/35.40               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 35.21/35.40                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 35.21/35.40  thf('45', plain,
% 35.21/35.40      (![X18 : $i, X19 : $i, X20 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X18 @ X19)
% 35.21/35.40          | ~ (m1_pre_topc @ X18 @ X20)
% 35.21/35.40          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 35.21/35.40          | ~ (m1_pre_topc @ X20 @ X19)
% 35.21/35.40          | ~ (l1_pre_topc @ X19)
% 35.21/35.40          | ~ (v2_pre_topc @ X19))),
% 35.21/35.40      inference('cnf', [status(esa)], [t4_tsep_1])).
% 35.21/35.40  thf('46', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v2_struct_0 @ sk_C)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B)
% 35.21/35.40          | ~ (v2_pre_topc @ sk_D)
% 35.21/35.40          | ~ (l1_pre_topc @ sk_D)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_D)
% 35.21/35.40          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 35.21/35.40             (u1_struct_0 @ X0))
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ X0))),
% 35.21/35.40      inference('sup-', [status(thm)], ['44', '45'])).
% 35.21/35.40  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf(cc1_pre_topc, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.21/35.40       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 35.21/35.40  thf('48', plain,
% 35.21/35.40      (![X0 : $i, X1 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X0 @ X1)
% 35.21/35.40          | (v2_pre_topc @ X0)
% 35.21/35.40          | ~ (l1_pre_topc @ X1)
% 35.21/35.40          | ~ (v2_pre_topc @ X1))),
% 35.21/35.40      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 35.21/35.40  thf('49', plain,
% 35.21/35.40      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['47', '48'])).
% 35.21/35.40  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('52', plain, ((v2_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['49', '50', '51'])).
% 35.21/35.40  thf('53', plain, ((l1_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['14', '15'])).
% 35.21/35.40  thf('54', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v2_struct_0 @ sk_C)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_D)
% 35.21/35.40          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 35.21/35.40             (u1_struct_0 @ X0))
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ X0))),
% 35.21/35.40      inference('demod', [status(thm)], ['46', '52', '53'])).
% 35.21/35.40  thf('55', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 35.21/35.40           (u1_struct_0 @ sk_D))
% 35.21/35.40        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('sup-', [status(thm)], ['43', '54'])).
% 35.21/35.40  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('57', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf(t22_tsep_1, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.21/35.40       ( ![B:$i]:
% 35.21/35.40         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 35.21/35.40           ( ![C:$i]:
% 35.21/35.40             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 35.21/35.40               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 35.21/35.40  thf('58', plain,
% 35.21/35.40      (![X13 : $i, X14 : $i, X15 : $i]:
% 35.21/35.40         ((v2_struct_0 @ X13)
% 35.21/35.40          | ~ (m1_pre_topc @ X13 @ X14)
% 35.21/35.40          | (m1_pre_topc @ X13 @ (k1_tsep_1 @ X14 @ X13 @ X15))
% 35.21/35.40          | ~ (m1_pre_topc @ X15 @ X14)
% 35.21/35.40          | (v2_struct_0 @ X15)
% 35.21/35.40          | ~ (l1_pre_topc @ X14)
% 35.21/35.40          | ~ (v2_pre_topc @ X14)
% 35.21/35.40          | (v2_struct_0 @ X14))),
% 35.21/35.40      inference('cnf', [status(esa)], [t22_tsep_1])).
% 35.21/35.40  thf('59', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v2_struct_0 @ sk_A)
% 35.21/35.40          | ~ (v2_pre_topc @ sk_A)
% 35.21/35.40          | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_A)
% 35.21/35.40          | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 35.21/35.40          | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['57', '58'])).
% 35.21/35.40  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('62', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v2_struct_0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_A)
% 35.21/35.40          | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 35.21/35.40          | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('demod', [status(thm)], ['59', '60', '61'])).
% 35.21/35.40  thf('63', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_D)
% 35.21/35.40        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_A))),
% 35.21/35.40      inference('sup-', [status(thm)], ['56', '62'])).
% 35.21/35.40  thf('64', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_A)
% 35.21/35.40        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 35.21/35.40        | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('simplify', [status(thm)], ['63'])).
% 35.21/35.40  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('66', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_D)
% 35.21/35.40        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 35.21/35.40      inference('clc', [status(thm)], ['64', '65'])).
% 35.21/35.40  thf('67', plain, (~ (v2_struct_0 @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('68', plain, ((m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 35.21/35.40      inference('clc', [status(thm)], ['66', '67'])).
% 35.21/35.40  thf('69', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf(t25_tmap_1, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.21/35.40       ( ![B:$i]:
% 35.21/35.40         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 35.21/35.40           ( ( k1_tsep_1 @ A @ B @ B ) =
% 35.21/35.40             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 35.21/35.40  thf('70', plain,
% 35.21/35.40      (![X16 : $i, X17 : $i]:
% 35.21/35.40         ((v2_struct_0 @ X16)
% 35.21/35.40          | ~ (m1_pre_topc @ X16 @ X17)
% 35.21/35.40          | ((k1_tsep_1 @ X17 @ X16 @ X16)
% 35.21/35.40              = (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 35.21/35.40          | ~ (l1_pre_topc @ X17)
% 35.21/35.40          | ~ (v2_pre_topc @ X17)
% 35.21/35.40          | (v2_struct_0 @ X17))),
% 35.21/35.40      inference('cnf', [status(esa)], [t25_tmap_1])).
% 35.21/35.40  thf('71', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_A)
% 35.21/35.40        | ~ (v2_pre_topc @ sk_A)
% 35.21/35.40        | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 35.21/35.40            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 35.21/35.40        | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['69', '70'])).
% 35.21/35.40  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('74', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_A)
% 35.21/35.40        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 35.21/35.40            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 35.21/35.40        | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('demod', [status(thm)], ['71', '72', '73'])).
% 35.21/35.40  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('76', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_D)
% 35.21/35.40        | ((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 35.21/35.40            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 35.21/35.40      inference('clc', [status(thm)], ['74', '75'])).
% 35.21/35.40  thf('77', plain, (~ (v2_struct_0 @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('78', plain,
% 35.21/35.40      (((k1_tsep_1 @ sk_A @ sk_D @ sk_D)
% 35.21/35.40         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 35.21/35.40      inference('clc', [status(thm)], ['76', '77'])).
% 35.21/35.40  thf(t59_pre_topc, axiom,
% 35.21/35.40    (![A:$i]:
% 35.21/35.40     ( ( l1_pre_topc @ A ) =>
% 35.21/35.40       ( ![B:$i]:
% 35.21/35.40         ( ( m1_pre_topc @
% 35.21/35.40             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 35.21/35.40           ( m1_pre_topc @ B @ A ) ) ) ))).
% 35.21/35.40  thf('79', plain,
% 35.21/35.40      (![X4 : $i, X5 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X4 @ 
% 35.21/35.40             (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 35.21/35.40          | (m1_pre_topc @ X4 @ X5)
% 35.21/35.40          | ~ (l1_pre_topc @ X5))),
% 35.21/35.40      inference('cnf', [status(esa)], [t59_pre_topc])).
% 35.21/35.40  thf('80', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 35.21/35.40          | ~ (l1_pre_topc @ sk_D)
% 35.21/35.40          | (m1_pre_topc @ X0 @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['78', '79'])).
% 35.21/35.40  thf('81', plain, ((l1_pre_topc @ sk_D)),
% 35.21/35.40      inference('demod', [status(thm)], ['14', '15'])).
% 35.21/35.40  thf('82', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 35.21/35.40          | (m1_pre_topc @ X0 @ sk_D))),
% 35.21/35.40      inference('demod', [status(thm)], ['80', '81'])).
% 35.21/35.40  thf('83', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 35.21/35.40      inference('sup-', [status(thm)], ['68', '82'])).
% 35.21/35.40  thf('84', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 35.21/35.40           (u1_struct_0 @ sk_D))
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('demod', [status(thm)], ['55', '83'])).
% 35.21/35.40  thf('85', plain,
% 35.21/35.40      (((r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 35.21/35.40         (u1_struct_0 @ sk_D))
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['84'])).
% 35.21/35.40  thf('86', plain,
% 35.21/35.40      (((r1_tarski @ 
% 35.21/35.40         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 35.21/35.40         (u1_struct_0 @ sk_D))
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('sup+', [status(thm)], ['42', '85'])).
% 35.21/35.40  thf('87', plain,
% 35.21/35.40      (((r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (r1_tarski @ 
% 35.21/35.40           (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 35.21/35.40           (u1_struct_0 @ sk_D)))),
% 35.21/35.40      inference('simplify', [status(thm)], ['86'])).
% 35.21/35.40  thf('88', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('90', plain,
% 35.21/35.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X10 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X10)
% 35.21/35.40          | ~ (l1_pre_topc @ X11)
% 35.21/35.40          | (v2_struct_0 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X12)
% 35.21/35.40          | ~ (m1_pre_topc @ X12 @ X11)
% 35.21/35.40          | (v1_pre_topc @ (k2_tsep_1 @ X11 @ X10 @ X12)))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 35.21/35.40  thf('91', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_A)
% 35.21/35.40          | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('sup-', [status(thm)], ['89', '90'])).
% 35.21/35.40  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('93', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ X0)
% 35.21/35.40          | (v2_struct_0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('demod', [status(thm)], ['91', '92'])).
% 35.21/35.40  thf('94', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 35.21/35.40      inference('sup-', [status(thm)], ['88', '93'])).
% 35.21/35.40  thf('95', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 35.21/35.40      inference('sup-', [status(thm)], ['1', '6'])).
% 35.21/35.40  thf('96', plain,
% 35.21/35.40      (![X6 : $i, X7 : $i, X8 : $i]:
% 35.21/35.40         ((v2_struct_0 @ X7)
% 35.21/35.40          | ~ (l1_pre_topc @ X7)
% 35.21/35.40          | (v2_struct_0 @ X8)
% 35.21/35.40          | ~ (m1_pre_topc @ X8 @ X7)
% 35.21/35.40          | ((u1_struct_0 @ (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40              = (k3_xboole_0 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X8)))
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ X7 @ X6 @ X8) @ X7)
% 35.21/35.40          | ~ (v1_pre_topc @ (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40          | (v2_struct_0 @ (k2_tsep_1 @ X7 @ X6 @ X8))
% 35.21/35.40          | (r1_tsep_1 @ X6 @ X8)
% 35.21/35.40          | ~ (m1_pre_topc @ X6 @ X7)
% 35.21/35.40          | (v2_struct_0 @ X6))),
% 35.21/35.40      inference('simplify', [status(thm)], ['26'])).
% 35.21/35.40  thf('97', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_A))),
% 35.21/35.40      inference('sup-', [status(thm)], ['95', '96'])).
% 35.21/35.40  thf('98', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('99', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('101', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A))),
% 35.21/35.40      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 35.21/35.40  thf('102', plain,
% 35.21/35.40      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['101'])).
% 35.21/35.40  thf('103', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 35.21/35.40      inference('sup-', [status(thm)], ['94', '102'])).
% 35.21/35.40  thf('104', plain,
% 35.21/35.40      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['103'])).
% 35.21/35.40  thf('105', plain,
% 35.21/35.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X10 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X10)
% 35.21/35.40          | ~ (l1_pre_topc @ X11)
% 35.21/35.40          | (v2_struct_0 @ X11)
% 35.21/35.40          | (v2_struct_0 @ X12)
% 35.21/35.40          | ~ (m1_pre_topc @ X12 @ X11)
% 35.21/35.40          | ~ (v2_struct_0 @ (k2_tsep_1 @ X11 @ X10 @ X12)))),
% 35.21/35.40      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 35.21/35.40  thf('106', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 35.21/35.40      inference('sup-', [status(thm)], ['104', '105'])).
% 35.21/35.40  thf('107', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('109', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('110', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 35.21/35.40  thf('111', plain,
% 35.21/35.40      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 35.21/35.40          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['110'])).
% 35.21/35.40  thf('112', plain,
% 35.21/35.40      (![X18 : $i, X19 : $i, X20 : $i]:
% 35.21/35.40         (~ (m1_pre_topc @ X18 @ X19)
% 35.21/35.40          | ~ (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 35.21/35.40          | (m1_pre_topc @ X18 @ X20)
% 35.21/35.40          | ~ (m1_pre_topc @ X20 @ X19)
% 35.21/35.40          | ~ (l1_pre_topc @ X19)
% 35.21/35.40          | ~ (v2_pre_topc @ X19))),
% 35.21/35.40      inference('cnf', [status(esa)], [t4_tsep_1])).
% 35.21/35.40  thf('113', plain,
% 35.21/35.40      (![X0 : $i, X1 : $i]:
% 35.21/35.40         (~ (r1_tarski @ 
% 35.21/35.40             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 35.21/35.40             (u1_struct_0 @ X0))
% 35.21/35.40          | (v2_struct_0 @ sk_C)
% 35.21/35.40          | (v2_struct_0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ sk_B)
% 35.21/35.40          | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40          | ~ (v2_pre_topc @ X1)
% 35.21/35.40          | ~ (l1_pre_topc @ X1)
% 35.21/35.40          | ~ (m1_pre_topc @ X0 @ X1)
% 35.21/35.40          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 35.21/35.40      inference('sup-', [status(thm)], ['111', '112'])).
% 35.21/35.40  thf('114', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v2_struct_0 @ sk_C)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_B)
% 35.21/35.40          | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 35.21/35.40          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 35.21/35.40          | ~ (m1_pre_topc @ sk_D @ X0)
% 35.21/35.40          | ~ (l1_pre_topc @ X0)
% 35.21/35.40          | ~ (v2_pre_topc @ X0)
% 35.21/35.40          | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40          | (v2_struct_0 @ sk_B)
% 35.21/35.40          | (v2_struct_0 @ sk_A)
% 35.21/35.40          | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('sup-', [status(thm)], ['87', '113'])).
% 35.21/35.40  thf('115', plain,
% 35.21/35.40      (![X0 : $i]:
% 35.21/35.40         ((v2_struct_0 @ sk_A)
% 35.21/35.40          | ~ (v2_pre_topc @ X0)
% 35.21/35.40          | ~ (l1_pre_topc @ X0)
% 35.21/35.40          | ~ (m1_pre_topc @ sk_D @ X0)
% 35.21/35.40          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 35.21/35.40          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 35.21/35.40          | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40          | (v2_struct_0 @ sk_B)
% 35.21/35.40          | (v2_struct_0 @ sk_D)
% 35.21/35.40          | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['114'])).
% 35.21/35.40  thf('116', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 35.21/35.40        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 35.21/35.40        | ~ (l1_pre_topc @ sk_A)
% 35.21/35.40        | ~ (v2_pre_topc @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_A))),
% 35.21/35.40      inference('sup-', [status(thm)], ['7', '115'])).
% 35.21/35.40  thf('117', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('120', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_A))),
% 35.21/35.40      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 35.21/35.40  thf('121', plain,
% 35.21/35.40      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('simplify', [status(thm)], ['120'])).
% 35.21/35.40  thf('122', plain,
% 35.21/35.40      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('123', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_D)
% 35.21/35.40        | (r1_tsep_1 @ sk_B @ sk_C))),
% 35.21/35.40      inference('sup-', [status(thm)], ['121', '122'])).
% 35.21/35.40  thf('124', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('125', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_D)
% 35.21/35.40        | (v2_struct_0 @ sk_B)
% 35.21/35.40        | (v2_struct_0 @ sk_A)
% 35.21/35.40        | (v2_struct_0 @ sk_C))),
% 35.21/35.40      inference('sup-', [status(thm)], ['123', '124'])).
% 35.21/35.40  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('127', plain,
% 35.21/35.40      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 35.21/35.40      inference('sup-', [status(thm)], ['125', '126'])).
% 35.21/35.40  thf('128', plain, (~ (v2_struct_0 @ sk_C)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('129', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 35.21/35.40      inference('clc', [status(thm)], ['127', '128'])).
% 35.21/35.40  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 35.21/35.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.21/35.40  thf('131', plain, ((v2_struct_0 @ sk_B)),
% 35.21/35.40      inference('clc', [status(thm)], ['129', '130'])).
% 35.21/35.40  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 35.21/35.40  
% 35.21/35.40  % SZS output end Refutation
% 35.21/35.40  
% 35.21/35.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
