%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mRNFAaIlxi

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:29 EST 2020

% Result     : Theorem 13.12s
% Output     : Refutation 13.12s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 252 expanded)
%              Number of leaves         :   22 (  79 expanded)
%              Depth                    :   26
%              Number of atoms          : 1437 (4856 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( X7
       != ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ( ( u1_struct_0 @ X7 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
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
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
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
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C @ sk_B @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
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
      | ( v1_pre_topc @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
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
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X6 @ X5 @ X8 ) )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('61',plain,
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
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
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
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('70',plain,
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
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
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
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
    inference('sup-',[status(thm)],['51','77'])).

thf('79',plain,(
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
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
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
    inference('sup-',[status(thm)],['7','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mRNFAaIlxi
% 0.16/0.37  % Computer   : n005.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:33:48 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 13.12/13.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.12/13.34  % Solved by: fo/fo7.sh
% 13.12/13.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.12/13.34  % done 4656 iterations in 12.879s
% 13.12/13.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.12/13.34  % SZS output start Refutation
% 13.12/13.34  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 13.12/13.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.12/13.34  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 13.12/13.34  thf(sk_A_type, type, sk_A: $i).
% 13.12/13.34  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 13.12/13.34  thf(sk_C_type, type, sk_C: $i).
% 13.12/13.34  thf(sk_D_type, type, sk_D: $i).
% 13.12/13.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.12/13.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 13.12/13.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.12/13.34  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 13.12/13.34  thf(sk_B_type, type, sk_B: $i).
% 13.12/13.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 13.12/13.34  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 13.12/13.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.12/13.34  thf(t29_tmap_1, conjecture,
% 13.12/13.34    (![A:$i]:
% 13.12/13.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.12/13.34       ( ![B:$i]:
% 13.12/13.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.12/13.34           ( ![C:$i]:
% 13.12/13.34             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.12/13.34               ( ![D:$i]:
% 13.12/13.34                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 13.12/13.34                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 13.12/13.34                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 13.12/13.34  thf(zf_stmt_0, negated_conjecture,
% 13.12/13.34    (~( ![A:$i]:
% 13.12/13.34        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 13.12/13.34            ( l1_pre_topc @ A ) ) =>
% 13.12/13.34          ( ![B:$i]:
% 13.12/13.34            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.12/13.34              ( ![C:$i]:
% 13.12/13.34                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.12/13.34                  ( ![D:$i]:
% 13.12/13.34                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 13.12/13.34                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 13.12/13.34                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 13.12/13.34    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 13.12/13.34  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf(dt_k1_tsep_1, axiom,
% 13.12/13.34    (![A:$i,B:$i,C:$i]:
% 13.12/13.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 13.12/13.34         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 13.12/13.34         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.12/13.34       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 13.12/13.34         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 13.12/13.34         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 13.12/13.34  thf('3', plain,
% 13.12/13.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X9 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X9)
% 13.12/13.34          | ~ (l1_pre_topc @ X10)
% 13.12/13.34          | (v2_struct_0 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X11)
% 13.12/13.34          | ~ (m1_pre_topc @ X11 @ X10)
% 13.12/13.34          | (m1_pre_topc @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 13.12/13.34  thf('4', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_A)
% 13.12/13.34          | ~ (l1_pre_topc @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('sup-', [status(thm)], ['2', '3'])).
% 13.12/13.34  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('6', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('demod', [status(thm)], ['4', '5'])).
% 13.12/13.34  thf('7', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 13.12/13.34      inference('sup-', [status(thm)], ['1', '6'])).
% 13.12/13.34  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('10', plain,
% 13.12/13.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X9 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X9)
% 13.12/13.34          | ~ (l1_pre_topc @ X10)
% 13.12/13.34          | (v2_struct_0 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X11)
% 13.12/13.34          | ~ (m1_pre_topc @ X11 @ X10)
% 13.12/13.34          | (v1_pre_topc @ (k1_tsep_1 @ X10 @ X9 @ X11)))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 13.12/13.34  thf('11', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_C)
% 13.12/13.34          | ~ (l1_pre_topc @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('sup-', [status(thm)], ['9', '10'])).
% 13.12/13.34  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf(dt_m1_pre_topc, axiom,
% 13.12/13.34    (![A:$i]:
% 13.12/13.34     ( ( l1_pre_topc @ A ) =>
% 13.12/13.34       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 13.12/13.34  thf('13', plain,
% 13.12/13.34      (![X3 : $i, X4 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 13.12/13.34  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 13.12/13.34      inference('sup-', [status(thm)], ['12', '13'])).
% 13.12/13.34  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 13.12/13.34      inference('demod', [status(thm)], ['14', '15'])).
% 13.12/13.34  thf('17', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0))
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('demod', [status(thm)], ['11', '16'])).
% 13.12/13.34  thf('18', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)))),
% 13.12/13.34      inference('sup-', [status(thm)], ['8', '17'])).
% 13.12/13.34  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('21', plain,
% 13.12/13.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X9 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X9)
% 13.12/13.34          | ~ (l1_pre_topc @ X10)
% 13.12/13.34          | (v2_struct_0 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X11)
% 13.12/13.34          | ~ (m1_pre_topc @ X11 @ X10)
% 13.12/13.34          | (m1_pre_topc @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 13.12/13.34  thf('22', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_C)
% 13.12/13.34          | ~ (l1_pre_topc @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('sup-', [status(thm)], ['20', '21'])).
% 13.12/13.34  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 13.12/13.34      inference('demod', [status(thm)], ['14', '15'])).
% 13.12/13.34  thf('24', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ X0) @ sk_C)
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('demod', [status(thm)], ['22', '23'])).
% 13.12/13.34  thf('25', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 13.12/13.34      inference('sup-', [status(thm)], ['19', '24'])).
% 13.12/13.34  thf(d2_tsep_1, axiom,
% 13.12/13.34    (![A:$i]:
% 13.12/13.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 13.12/13.34       ( ![B:$i]:
% 13.12/13.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.12/13.34           ( ![C:$i]:
% 13.12/13.34             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.12/13.34               ( ![D:$i]:
% 13.12/13.34                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 13.12/13.34                     ( m1_pre_topc @ D @ A ) ) =>
% 13.12/13.34                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 13.12/13.34                     ( ( u1_struct_0 @ D ) =
% 13.12/13.34                       ( k2_xboole_0 @
% 13.12/13.34                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 13.12/13.34  thf('26', plain,
% 13.12/13.34      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 13.12/13.34         ((v2_struct_0 @ X5)
% 13.12/13.34          | ~ (m1_pre_topc @ X5 @ X6)
% 13.12/13.34          | (v2_struct_0 @ X7)
% 13.12/13.34          | ~ (v1_pre_topc @ X7)
% 13.12/13.34          | ~ (m1_pre_topc @ X7 @ X6)
% 13.12/13.34          | ((X7) != (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34          | ((u1_struct_0 @ X7)
% 13.12/13.34              = (k2_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X8)))
% 13.12/13.34          | ~ (m1_pre_topc @ X8 @ X6)
% 13.12/13.34          | (v2_struct_0 @ X8)
% 13.12/13.34          | ~ (l1_pre_topc @ X6)
% 13.12/13.34          | (v2_struct_0 @ X6))),
% 13.12/13.34      inference('cnf', [status(esa)], [d2_tsep_1])).
% 13.12/13.34  thf('27', plain,
% 13.12/13.34      (![X5 : $i, X6 : $i, X8 : $i]:
% 13.12/13.34         ((v2_struct_0 @ X6)
% 13.12/13.34          | ~ (l1_pre_topc @ X6)
% 13.12/13.34          | (v2_struct_0 @ X8)
% 13.12/13.34          | ~ (m1_pre_topc @ X8 @ X6)
% 13.12/13.34          | ((u1_struct_0 @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34              = (k2_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X8)))
% 13.12/13.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ X6 @ X5 @ X8) @ X6)
% 13.12/13.34          | ~ (v1_pre_topc @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34          | (v2_struct_0 @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34          | ~ (m1_pre_topc @ X5 @ X6)
% 13.12/13.34          | (v2_struct_0 @ X5))),
% 13.12/13.34      inference('simplify', [status(thm)], ['26'])).
% 13.12/13.34  thf('28', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ~ (m1_pre_topc @ sk_B @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | ~ (l1_pre_topc @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_C))),
% 13.12/13.34      inference('sup-', [status(thm)], ['25', '27'])).
% 13.12/13.34  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 13.12/13.34      inference('demod', [status(thm)], ['14', '15'])).
% 13.12/13.34  thf('32', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C))),
% 13.12/13.34      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 13.12/13.34  thf('33', plain,
% 13.12/13.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['32'])).
% 13.12/13.34  thf('34', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 13.12/13.34      inference('sup-', [status(thm)], ['18', '33'])).
% 13.12/13.34  thf('35', plain,
% 13.12/13.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['34'])).
% 13.12/13.34  thf('36', plain,
% 13.12/13.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X9 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X9)
% 13.12/13.34          | ~ (l1_pre_topc @ X10)
% 13.12/13.34          | (v2_struct_0 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X11)
% 13.12/13.34          | ~ (m1_pre_topc @ X11 @ X10)
% 13.12/13.34          | ~ (v2_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 13.12/13.34  thf('37', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | ~ (l1_pre_topc @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ~ (m1_pre_topc @ sk_B @ sk_C))),
% 13.12/13.34      inference('sup-', [status(thm)], ['35', '36'])).
% 13.12/13.34  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 13.12/13.34      inference('demod', [status(thm)], ['14', '15'])).
% 13.12/13.34  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('41', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 13.12/13.34  thf('42', plain,
% 13.12/13.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D))
% 13.12/13.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['41'])).
% 13.12/13.34  thf('43', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D) @ sk_C))),
% 13.12/13.34      inference('sup-', [status(thm)], ['19', '24'])).
% 13.12/13.34  thf(t1_tsep_1, axiom,
% 13.12/13.34    (![A:$i]:
% 13.12/13.34     ( ( l1_pre_topc @ A ) =>
% 13.12/13.34       ( ![B:$i]:
% 13.12/13.34         ( ( m1_pre_topc @ B @ A ) =>
% 13.12/13.34           ( m1_subset_1 @
% 13.12/13.34             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 13.12/13.34  thf('44', plain,
% 13.12/13.34      (![X12 : $i, X13 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X12 @ X13)
% 13.12/13.34          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 13.12/13.34             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 13.12/13.34          | ~ (l1_pre_topc @ X13))),
% 13.12/13.34      inference('cnf', [status(esa)], [t1_tsep_1])).
% 13.12/13.34  thf('45', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ~ (l1_pre_topc @ sk_C)
% 13.12/13.34        | (m1_subset_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 13.12/13.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 13.12/13.34      inference('sup-', [status(thm)], ['43', '44'])).
% 13.12/13.34  thf('46', plain, ((l1_pre_topc @ sk_C)),
% 13.12/13.34      inference('demod', [status(thm)], ['14', '15'])).
% 13.12/13.34  thf('47', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (m1_subset_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 13.12/13.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 13.12/13.34      inference('demod', [status(thm)], ['45', '46'])).
% 13.12/13.34  thf(t3_subset, axiom,
% 13.12/13.34    (![A:$i,B:$i]:
% 13.12/13.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.12/13.34  thf('48', plain,
% 13.12/13.34      (![X0 : $i, X1 : $i]:
% 13.12/13.34         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 13.12/13.34      inference('cnf', [status(esa)], [t3_subset])).
% 13.12/13.34  thf('49', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C @ sk_B @ sk_D)) @ 
% 13.12/13.34           (u1_struct_0 @ sk_C)))),
% 13.12/13.34      inference('sup-', [status(thm)], ['47', '48'])).
% 13.12/13.34  thf('50', plain,
% 13.12/13.34      (((r1_tarski @ 
% 13.12/13.34         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 13.12/13.34         (u1_struct_0 @ sk_C))
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('sup+', [status(thm)], ['42', '49'])).
% 13.12/13.34  thf('51', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (r1_tarski @ 
% 13.12/13.34           (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 13.12/13.34           (u1_struct_0 @ sk_C)))),
% 13.12/13.34      inference('simplify', [status(thm)], ['50'])).
% 13.12/13.34  thf('52', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('54', plain,
% 13.12/13.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X9 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X9)
% 13.12/13.34          | ~ (l1_pre_topc @ X10)
% 13.12/13.34          | (v2_struct_0 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X11)
% 13.12/13.34          | ~ (m1_pre_topc @ X11 @ X10)
% 13.12/13.34          | (v1_pre_topc @ (k1_tsep_1 @ X10 @ X9 @ X11)))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 13.12/13.34  thf('55', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_A)
% 13.12/13.34          | ~ (l1_pre_topc @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('sup-', [status(thm)], ['53', '54'])).
% 13.12/13.34  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('57', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('demod', [status(thm)], ['55', '56'])).
% 13.12/13.34  thf('58', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 13.12/13.34      inference('sup-', [status(thm)], ['52', '57'])).
% 13.12/13.34  thf('59', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 13.12/13.34      inference('sup-', [status(thm)], ['1', '6'])).
% 13.12/13.34  thf('60', plain,
% 13.12/13.34      (![X5 : $i, X6 : $i, X8 : $i]:
% 13.12/13.34         ((v2_struct_0 @ X6)
% 13.12/13.34          | ~ (l1_pre_topc @ X6)
% 13.12/13.34          | (v2_struct_0 @ X8)
% 13.12/13.34          | ~ (m1_pre_topc @ X8 @ X6)
% 13.12/13.34          | ((u1_struct_0 @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34              = (k2_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X8)))
% 13.12/13.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ X6 @ X5 @ X8) @ X6)
% 13.12/13.34          | ~ (v1_pre_topc @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34          | (v2_struct_0 @ (k1_tsep_1 @ X6 @ X5 @ X8))
% 13.12/13.34          | ~ (m1_pre_topc @ X5 @ X6)
% 13.12/13.34          | (v2_struct_0 @ X5))),
% 13.12/13.34      inference('simplify', [status(thm)], ['26'])).
% 13.12/13.34  thf('61', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | ~ (l1_pre_topc @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_A))),
% 13.12/13.34      inference('sup-', [status(thm)], ['59', '60'])).
% 13.12/13.34  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('65', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A))),
% 13.12/13.34      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 13.12/13.34  thf('66', plain,
% 13.12/13.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['65'])).
% 13.12/13.34  thf('67', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 13.12/13.34      inference('sup-', [status(thm)], ['58', '66'])).
% 13.12/13.34  thf('68', plain,
% 13.12/13.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['67'])).
% 13.12/13.34  thf('69', plain,
% 13.12/13.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X9 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X9)
% 13.12/13.34          | ~ (l1_pre_topc @ X10)
% 13.12/13.34          | (v2_struct_0 @ X10)
% 13.12/13.34          | (v2_struct_0 @ X11)
% 13.12/13.34          | ~ (m1_pre_topc @ X11 @ X10)
% 13.12/13.34          | ~ (v2_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)))),
% 13.12/13.34      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 13.12/13.34  thf('70', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | ~ (l1_pre_topc @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 13.12/13.34      inference('sup-', [status(thm)], ['68', '69'])).
% 13.12/13.34  thf('71', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('74', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 13.12/13.34  thf('75', plain,
% 13.12/13.34      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 13.12/13.34          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['74'])).
% 13.12/13.34  thf(t4_tsep_1, axiom,
% 13.12/13.34    (![A:$i]:
% 13.12/13.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.12/13.34       ( ![B:$i]:
% 13.12/13.34         ( ( m1_pre_topc @ B @ A ) =>
% 13.12/13.34           ( ![C:$i]:
% 13.12/13.34             ( ( m1_pre_topc @ C @ A ) =>
% 13.12/13.34               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 13.12/13.34                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 13.12/13.34  thf('76', plain,
% 13.12/13.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.12/13.34         (~ (m1_pre_topc @ X14 @ X15)
% 13.12/13.34          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 13.12/13.34          | (m1_pre_topc @ X14 @ X16)
% 13.12/13.34          | ~ (m1_pre_topc @ X16 @ X15)
% 13.12/13.34          | ~ (l1_pre_topc @ X15)
% 13.12/13.34          | ~ (v2_pre_topc @ X15))),
% 13.12/13.34      inference('cnf', [status(esa)], [t4_tsep_1])).
% 13.12/13.34  thf('77', plain,
% 13.12/13.34      (![X0 : $i, X1 : $i]:
% 13.12/13.34         (~ (r1_tarski @ 
% 13.12/13.34             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 13.12/13.34             (u1_struct_0 @ X0))
% 13.12/13.34          | (v2_struct_0 @ sk_D)
% 13.12/13.34          | (v2_struct_0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ sk_B)
% 13.12/13.34          | ~ (v2_pre_topc @ X1)
% 13.12/13.34          | ~ (l1_pre_topc @ X1)
% 13.12/13.34          | ~ (m1_pre_topc @ X0 @ X1)
% 13.12/13.34          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 13.12/13.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X1))),
% 13.12/13.34      inference('sup-', [status(thm)], ['75', '76'])).
% 13.12/13.34  thf('78', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((v2_struct_0 @ sk_D)
% 13.12/13.34          | (v2_struct_0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ sk_B)
% 13.12/13.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 13.12/13.34          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 13.12/13.34          | ~ (m1_pre_topc @ sk_C @ X0)
% 13.12/13.34          | ~ (l1_pre_topc @ X0)
% 13.12/13.34          | ~ (v2_pre_topc @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_B)
% 13.12/13.34          | (v2_struct_0 @ sk_A)
% 13.12/13.34          | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('sup-', [status(thm)], ['51', '77'])).
% 13.12/13.34  thf('79', plain,
% 13.12/13.34      (![X0 : $i]:
% 13.12/13.34         ((v2_struct_0 @ sk_A)
% 13.12/13.34          | ~ (v2_pre_topc @ X0)
% 13.12/13.34          | ~ (l1_pre_topc @ X0)
% 13.12/13.34          | ~ (m1_pre_topc @ sk_C @ X0)
% 13.12/13.34          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 13.12/13.34          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 13.12/13.34          | (v2_struct_0 @ sk_B)
% 13.12/13.34          | (v2_struct_0 @ sk_C)
% 13.12/13.34          | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['78'])).
% 13.12/13.34  thf('80', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 13.12/13.34        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 13.12/13.34        | ~ (l1_pre_topc @ sk_A)
% 13.12/13.34        | ~ (v2_pre_topc @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_A))),
% 13.12/13.34      inference('sup-', [status(thm)], ['7', '79'])).
% 13.12/13.34  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('84', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_A))),
% 13.12/13.34      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 13.12/13.34  thf('85', plain,
% 13.12/13.34      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_C)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('simplify', [status(thm)], ['84'])).
% 13.12/13.34  thf('86', plain, (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('87', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_D)
% 13.12/13.34        | (v2_struct_0 @ sk_A)
% 13.12/13.34        | (v2_struct_0 @ sk_B)
% 13.12/13.34        | (v2_struct_0 @ sk_C))),
% 13.12/13.34      inference('sup-', [status(thm)], ['85', '86'])).
% 13.12/13.34  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('89', plain,
% 13.12/13.34      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 13.12/13.34      inference('sup-', [status(thm)], ['87', '88'])).
% 13.12/13.34  thf('90', plain, (~ (v2_struct_0 @ sk_C)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('91', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 13.12/13.34      inference('clc', [status(thm)], ['89', '90'])).
% 13.12/13.34  thf('92', plain, (~ (v2_struct_0 @ sk_D)),
% 13.12/13.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.12/13.34  thf('93', plain, ((v2_struct_0 @ sk_B)),
% 13.12/13.34      inference('clc', [status(thm)], ['91', '92'])).
% 13.12/13.34  thf('94', plain, ($false), inference('demod', [status(thm)], ['0', '93'])).
% 13.12/13.34  
% 13.12/13.34  % SZS output end Refutation
% 13.12/13.34  
% 13.12/13.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
