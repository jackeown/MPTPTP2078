%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wrrz8MNP4x

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:31 EST 2020

% Result     : Theorem 31.67s
% Output     : Refutation 31.67s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 257 expanded)
%              Number of leaves         :   23 (  81 expanded)
%              Depth                    :   27
%              Number of atoms          : 1544 (5305 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( X8
       != ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( ( u1_struct_0 @ X8 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
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

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_D @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('61',plain,
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
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
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
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
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
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('70',plain,
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

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

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) )
      | ( m1_pre_topc @ X14 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('77',plain,(
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
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
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
    inference('sup-',[status(thm)],['51','77'])).

thf('79',plain,(
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
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
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
    inference('sup-',[status(thm)],['7','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wrrz8MNP4x
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 31.67/31.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.67/31.87  % Solved by: fo/fo7.sh
% 31.67/31.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.67/31.87  % done 6709 iterations in 31.397s
% 31.67/31.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.67/31.87  % SZS output start Refutation
% 31.67/31.87  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 31.67/31.87  thf(sk_C_type, type, sk_C: $i).
% 31.67/31.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.67/31.87  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 31.67/31.87  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 31.67/31.87  thf(sk_B_type, type, sk_B: $i).
% 31.67/31.87  thf(sk_A_type, type, sk_A: $i).
% 31.67/31.87  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 31.67/31.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 31.67/31.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 31.67/31.87  thf(sk_D_type, type, sk_D: $i).
% 31.67/31.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 31.67/31.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.67/31.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 31.67/31.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 31.67/31.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.67/31.87  thf(t30_tmap_1, conjecture,
% 31.67/31.87    (![A:$i]:
% 31.67/31.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 31.67/31.87       ( ![B:$i]:
% 31.67/31.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 31.67/31.87           ( ![C:$i]:
% 31.67/31.87             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 31.67/31.87               ( ![D:$i]:
% 31.67/31.87                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 31.67/31.87                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 31.67/31.87                     ( ( r1_tsep_1 @ B @ C ) | 
% 31.67/31.87                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 31.67/31.87  thf(zf_stmt_0, negated_conjecture,
% 31.67/31.87    (~( ![A:$i]:
% 31.67/31.87        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 31.67/31.87            ( l1_pre_topc @ A ) ) =>
% 31.67/31.87          ( ![B:$i]:
% 31.67/31.87            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 31.67/31.87              ( ![C:$i]:
% 31.67/31.87                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 31.67/31.87                  ( ![D:$i]:
% 31.67/31.87                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 31.67/31.87                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 31.67/31.87                        ( ( r1_tsep_1 @ B @ C ) | 
% 31.67/31.87                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 31.67/31.87    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 31.67/31.87  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf(dt_k2_tsep_1, axiom,
% 31.67/31.87    (![A:$i,B:$i,C:$i]:
% 31.67/31.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 31.67/31.87         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 31.67/31.87         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 31.67/31.87       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 31.67/31.87         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 31.67/31.87         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 31.67/31.87  thf('3', plain,
% 31.67/31.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X9 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X9)
% 31.67/31.87          | ~ (l1_pre_topc @ X10)
% 31.67/31.87          | (v2_struct_0 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X11)
% 31.67/31.87          | ~ (m1_pre_topc @ X11 @ X10)
% 31.67/31.87          | (m1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 31.67/31.87  thf('4', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_A)
% 31.67/31.87          | ~ (l1_pre_topc @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('sup-', [status(thm)], ['2', '3'])).
% 31.67/31.87  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('6', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('demod', [status(thm)], ['4', '5'])).
% 31.67/31.87  thf('7', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 31.67/31.87      inference('sup-', [status(thm)], ['1', '6'])).
% 31.67/31.87  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('10', plain,
% 31.67/31.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X9 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X9)
% 31.67/31.87          | ~ (l1_pre_topc @ X10)
% 31.67/31.87          | (v2_struct_0 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X11)
% 31.67/31.87          | ~ (m1_pre_topc @ X11 @ X10)
% 31.67/31.87          | (v1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 31.67/31.87  thf('11', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0))
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_D)
% 31.67/31.87          | ~ (l1_pre_topc @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('sup-', [status(thm)], ['9', '10'])).
% 31.67/31.87  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf(dt_m1_pre_topc, axiom,
% 31.67/31.87    (![A:$i]:
% 31.67/31.87     ( ( l1_pre_topc @ A ) =>
% 31.67/31.87       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 31.67/31.87  thf('13', plain,
% 31.67/31.87      (![X3 : $i, X4 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 31.67/31.87  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 31.67/31.87      inference('sup-', [status(thm)], ['12', '13'])).
% 31.67/31.87  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 31.67/31.87      inference('demod', [status(thm)], ['14', '15'])).
% 31.67/31.87  thf('17', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0))
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('demod', [status(thm)], ['11', '16'])).
% 31.67/31.87  thf('18', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)))),
% 31.67/31.87      inference('sup-', [status(thm)], ['8', '17'])).
% 31.67/31.87  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('21', plain,
% 31.67/31.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X9 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X9)
% 31.67/31.87          | ~ (l1_pre_topc @ X10)
% 31.67/31.87          | (v2_struct_0 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X11)
% 31.67/31.87          | ~ (m1_pre_topc @ X11 @ X10)
% 31.67/31.87          | (m1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 31.67/31.87  thf('22', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0) @ sk_D)
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_D)
% 31.67/31.87          | ~ (l1_pre_topc @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('sup-', [status(thm)], ['20', '21'])).
% 31.67/31.87  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 31.67/31.87      inference('demod', [status(thm)], ['14', '15'])).
% 31.67/31.87  thf('24', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ X0) @ sk_D)
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('demod', [status(thm)], ['22', '23'])).
% 31.67/31.87  thf('25', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 31.67/31.87      inference('sup-', [status(thm)], ['19', '24'])).
% 31.67/31.87  thf(d5_tsep_1, axiom,
% 31.67/31.87    (![A:$i]:
% 31.67/31.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 31.67/31.87       ( ![B:$i]:
% 31.67/31.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 31.67/31.87           ( ![C:$i]:
% 31.67/31.87             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 31.67/31.87               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 31.67/31.87                 ( ![D:$i]:
% 31.67/31.87                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 31.67/31.87                       ( m1_pre_topc @ D @ A ) ) =>
% 31.67/31.87                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 31.67/31.87                       ( ( u1_struct_0 @ D ) =
% 31.67/31.87                         ( k3_xboole_0 @
% 31.67/31.87                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 31.67/31.87  thf('26', plain,
% 31.67/31.87      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 31.67/31.87         ((v2_struct_0 @ X5)
% 31.67/31.87          | ~ (m1_pre_topc @ X5 @ X6)
% 31.67/31.87          | (r1_tsep_1 @ X5 @ X7)
% 31.67/31.87          | (v2_struct_0 @ X8)
% 31.67/31.87          | ~ (v1_pre_topc @ X8)
% 31.67/31.87          | ~ (m1_pre_topc @ X8 @ X6)
% 31.67/31.87          | ((X8) != (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87          | ((u1_struct_0 @ X8)
% 31.67/31.87              = (k3_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X7)))
% 31.67/31.87          | ~ (m1_pre_topc @ X7 @ X6)
% 31.67/31.87          | (v2_struct_0 @ X7)
% 31.67/31.87          | ~ (l1_pre_topc @ X6)
% 31.67/31.87          | (v2_struct_0 @ X6))),
% 31.67/31.87      inference('cnf', [status(esa)], [d5_tsep_1])).
% 31.67/31.87  thf('27', plain,
% 31.67/31.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 31.67/31.87         ((v2_struct_0 @ X6)
% 31.67/31.87          | ~ (l1_pre_topc @ X6)
% 31.67/31.87          | (v2_struct_0 @ X7)
% 31.67/31.87          | ~ (m1_pre_topc @ X7 @ X6)
% 31.67/31.87          | ((u1_struct_0 @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87              = (k3_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X7)))
% 31.67/31.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X7) @ X6)
% 31.67/31.87          | ~ (v1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87          | (v2_struct_0 @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87          | (r1_tsep_1 @ X5 @ X7)
% 31.67/31.87          | ~ (m1_pre_topc @ X5 @ X6)
% 31.67/31.87          | (v2_struct_0 @ X5))),
% 31.67/31.87      inference('simplify', [status(thm)], ['26'])).
% 31.67/31.87  thf('28', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | ~ (m1_pre_topc @ sk_B @ sk_D)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | ~ (l1_pre_topc @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_D))),
% 31.67/31.87      inference('sup-', [status(thm)], ['25', '27'])).
% 31.67/31.87  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 31.67/31.87      inference('demod', [status(thm)], ['14', '15'])).
% 31.67/31.87  thf('32', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D))),
% 31.67/31.87      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 31.67/31.87  thf('33', plain,
% 31.67/31.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['32'])).
% 31.67/31.87  thf('34', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 31.67/31.87      inference('sup-', [status(thm)], ['18', '33'])).
% 31.67/31.87  thf('35', plain,
% 31.67/31.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['34'])).
% 31.67/31.87  thf('36', plain,
% 31.67/31.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X9 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X9)
% 31.67/31.87          | ~ (l1_pre_topc @ X10)
% 31.67/31.87          | (v2_struct_0 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X11)
% 31.67/31.87          | ~ (m1_pre_topc @ X11 @ X10)
% 31.67/31.87          | ~ (v2_struct_0 @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 31.67/31.87  thf('37', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | ~ (l1_pre_topc @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | ~ (m1_pre_topc @ sk_B @ sk_D))),
% 31.67/31.87      inference('sup-', [status(thm)], ['35', '36'])).
% 31.67/31.87  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 31.67/31.87      inference('demod', [status(thm)], ['14', '15'])).
% 31.67/31.87  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('41', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 31.67/31.87  thf('42', plain,
% 31.67/31.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C))
% 31.67/31.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['41'])).
% 31.67/31.87  thf('43', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C) @ sk_D))),
% 31.67/31.87      inference('sup-', [status(thm)], ['19', '24'])).
% 31.67/31.87  thf(t1_tsep_1, axiom,
% 31.67/31.87    (![A:$i]:
% 31.67/31.87     ( ( l1_pre_topc @ A ) =>
% 31.67/31.87       ( ![B:$i]:
% 31.67/31.87         ( ( m1_pre_topc @ B @ A ) =>
% 31.67/31.87           ( m1_subset_1 @
% 31.67/31.87             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 31.67/31.87  thf('44', plain,
% 31.67/31.87      (![X12 : $i, X13 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X12 @ X13)
% 31.67/31.87          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 31.67/31.87             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 31.67/31.87          | ~ (l1_pre_topc @ X13))),
% 31.67/31.87      inference('cnf', [status(esa)], [t1_tsep_1])).
% 31.67/31.87  thf('45', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | ~ (l1_pre_topc @ sk_D)
% 31.67/31.87        | (m1_subset_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 31.67/31.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 31.67/31.87      inference('sup-', [status(thm)], ['43', '44'])).
% 31.67/31.87  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 31.67/31.87      inference('demod', [status(thm)], ['14', '15'])).
% 31.67/31.87  thf('47', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (m1_subset_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 31.67/31.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 31.67/31.87      inference('demod', [status(thm)], ['45', '46'])).
% 31.67/31.87  thf(t3_subset, axiom,
% 31.67/31.87    (![A:$i,B:$i]:
% 31.67/31.87     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 31.67/31.87  thf('48', plain,
% 31.67/31.87      (![X0 : $i, X1 : $i]:
% 31.67/31.87         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 31.67/31.87      inference('cnf', [status(esa)], [t3_subset])).
% 31.67/31.87  thf('49', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_D @ sk_B @ sk_C)) @ 
% 31.67/31.87           (u1_struct_0 @ sk_D)))),
% 31.67/31.87      inference('sup-', [status(thm)], ['47', '48'])).
% 31.67/31.87  thf('50', plain,
% 31.67/31.87      (((r1_tarski @ 
% 31.67/31.87         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 31.67/31.87         (u1_struct_0 @ sk_D))
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('sup+', [status(thm)], ['42', '49'])).
% 31.67/31.87  thf('51', plain,
% 31.67/31.87      (((r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (r1_tarski @ 
% 31.67/31.87           (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 31.67/31.87           (u1_struct_0 @ sk_D)))),
% 31.67/31.87      inference('simplify', [status(thm)], ['50'])).
% 31.67/31.87  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('54', plain,
% 31.67/31.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X9 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X9)
% 31.67/31.87          | ~ (l1_pre_topc @ X10)
% 31.67/31.87          | (v2_struct_0 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X11)
% 31.67/31.87          | ~ (m1_pre_topc @ X11 @ X10)
% 31.67/31.87          | (v1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 31.67/31.87  thf('55', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_A)
% 31.67/31.87          | ~ (l1_pre_topc @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('sup-', [status(thm)], ['53', '54'])).
% 31.67/31.87  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('57', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ X0)
% 31.67/31.87          | (v2_struct_0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('demod', [status(thm)], ['55', '56'])).
% 31.67/31.87  thf('58', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 31.67/31.87      inference('sup-', [status(thm)], ['52', '57'])).
% 31.67/31.87  thf('59', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 31.67/31.87      inference('sup-', [status(thm)], ['1', '6'])).
% 31.67/31.87  thf('60', plain,
% 31.67/31.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 31.67/31.87         ((v2_struct_0 @ X6)
% 31.67/31.87          | ~ (l1_pre_topc @ X6)
% 31.67/31.87          | (v2_struct_0 @ X7)
% 31.67/31.87          | ~ (m1_pre_topc @ X7 @ X6)
% 31.67/31.87          | ((u1_struct_0 @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87              = (k3_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X7)))
% 31.67/31.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X7) @ X6)
% 31.67/31.87          | ~ (v1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87          | (v2_struct_0 @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 31.67/31.87          | (r1_tsep_1 @ X5 @ X7)
% 31.67/31.87          | ~ (m1_pre_topc @ X5 @ X6)
% 31.67/31.87          | (v2_struct_0 @ X5))),
% 31.67/31.87      inference('simplify', [status(thm)], ['26'])).
% 31.67/31.87  thf('61', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | ~ (l1_pre_topc @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_A))),
% 31.67/31.87      inference('sup-', [status(thm)], ['59', '60'])).
% 31.67/31.87  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('65', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A))),
% 31.67/31.87      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 31.67/31.87  thf('66', plain,
% 31.67/31.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['65'])).
% 31.67/31.87  thf('67', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 31.67/31.87      inference('sup-', [status(thm)], ['58', '66'])).
% 31.67/31.87  thf('68', plain,
% 31.67/31.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['67'])).
% 31.67/31.87  thf('69', plain,
% 31.67/31.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X9 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X9)
% 31.67/31.87          | ~ (l1_pre_topc @ X10)
% 31.67/31.87          | (v2_struct_0 @ X10)
% 31.67/31.87          | (v2_struct_0 @ X11)
% 31.67/31.87          | ~ (m1_pre_topc @ X11 @ X10)
% 31.67/31.87          | ~ (v2_struct_0 @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 31.67/31.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 31.67/31.87  thf('70', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | ~ (l1_pre_topc @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 31.67/31.87      inference('sup-', [status(thm)], ['68', '69'])).
% 31.67/31.87  thf('71', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('74', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 31.67/31.87  thf('75', plain,
% 31.67/31.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 31.67/31.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['74'])).
% 31.67/31.87  thf(t4_tsep_1, axiom,
% 31.67/31.87    (![A:$i]:
% 31.67/31.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 31.67/31.87       ( ![B:$i]:
% 31.67/31.87         ( ( m1_pre_topc @ B @ A ) =>
% 31.67/31.87           ( ![C:$i]:
% 31.67/31.87             ( ( m1_pre_topc @ C @ A ) =>
% 31.67/31.87               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 31.67/31.87                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 31.67/31.87  thf('76', plain,
% 31.67/31.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 31.67/31.87         (~ (m1_pre_topc @ X14 @ X15)
% 31.67/31.87          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 31.67/31.87          | (m1_pre_topc @ X14 @ X16)
% 31.67/31.87          | ~ (m1_pre_topc @ X16 @ X15)
% 31.67/31.87          | ~ (l1_pre_topc @ X15)
% 31.67/31.87          | ~ (v2_pre_topc @ X15))),
% 31.67/31.87      inference('cnf', [status(esa)], [t4_tsep_1])).
% 31.67/31.87  thf('77', plain,
% 31.67/31.87      (![X0 : $i, X1 : $i]:
% 31.67/31.87         (~ (r1_tarski @ 
% 31.67/31.87             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 31.67/31.87             (u1_struct_0 @ X0))
% 31.67/31.87          | (v2_struct_0 @ sk_C)
% 31.67/31.87          | (v2_struct_0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ sk_B)
% 31.67/31.87          | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87          | ~ (v2_pre_topc @ X1)
% 31.67/31.87          | ~ (l1_pre_topc @ X1)
% 31.67/31.87          | ~ (m1_pre_topc @ X0 @ X1)
% 31.67/31.87          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 31.67/31.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 31.67/31.87      inference('sup-', [status(thm)], ['75', '76'])).
% 31.67/31.87  thf('78', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((v2_struct_0 @ sk_C)
% 31.67/31.87          | (v2_struct_0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ sk_B)
% 31.67/31.87          | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 31.67/31.87          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 31.67/31.87          | ~ (m1_pre_topc @ sk_D @ X0)
% 31.67/31.87          | ~ (l1_pre_topc @ X0)
% 31.67/31.87          | ~ (v2_pre_topc @ X0)
% 31.67/31.87          | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87          | (v2_struct_0 @ sk_B)
% 31.67/31.87          | (v2_struct_0 @ sk_A)
% 31.67/31.87          | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('sup-', [status(thm)], ['51', '77'])).
% 31.67/31.87  thf('79', plain,
% 31.67/31.87      (![X0 : $i]:
% 31.67/31.87         ((v2_struct_0 @ sk_A)
% 31.67/31.87          | ~ (v2_pre_topc @ X0)
% 31.67/31.87          | ~ (l1_pre_topc @ X0)
% 31.67/31.87          | ~ (m1_pre_topc @ sk_D @ X0)
% 31.67/31.87          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 31.67/31.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 31.67/31.87          | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87          | (v2_struct_0 @ sk_B)
% 31.67/31.87          | (v2_struct_0 @ sk_D)
% 31.67/31.87          | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['78'])).
% 31.67/31.87  thf('80', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 31.67/31.87        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 31.67/31.87        | ~ (l1_pre_topc @ sk_A)
% 31.67/31.87        | ~ (v2_pre_topc @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_A))),
% 31.67/31.87      inference('sup-', [status(thm)], ['7', '79'])).
% 31.67/31.87  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('84', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_A))),
% 31.67/31.87      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 31.67/31.87  thf('85', plain,
% 31.67/31.87      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('simplify', [status(thm)], ['84'])).
% 31.67/31.87  thf('86', plain, (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('87', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_D)
% 31.67/31.87        | (r1_tsep_1 @ sk_B @ sk_C))),
% 31.67/31.87      inference('sup-', [status(thm)], ['85', '86'])).
% 31.67/31.87  thf('88', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('89', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_D)
% 31.67/31.87        | (v2_struct_0 @ sk_B)
% 31.67/31.87        | (v2_struct_0 @ sk_A)
% 31.67/31.87        | (v2_struct_0 @ sk_C))),
% 31.67/31.87      inference('sup-', [status(thm)], ['87', '88'])).
% 31.67/31.87  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('91', plain,
% 31.67/31.87      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 31.67/31.87      inference('sup-', [status(thm)], ['89', '90'])).
% 31.67/31.87  thf('92', plain, (~ (v2_struct_0 @ sk_C)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('93', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 31.67/31.87      inference('clc', [status(thm)], ['91', '92'])).
% 31.67/31.87  thf('94', plain, (~ (v2_struct_0 @ sk_D)),
% 31.67/31.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.67/31.87  thf('95', plain, ((v2_struct_0 @ sk_B)),
% 31.67/31.87      inference('clc', [status(thm)], ['93', '94'])).
% 31.67/31.87  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 31.67/31.87  
% 31.67/31.87  % SZS output end Refutation
% 31.67/31.87  
% 31.67/31.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
