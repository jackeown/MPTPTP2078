%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UmdMtcG3HY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:33 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  201 (4965 expanded)
%              Number of leaves         :   39 (1487 expanded)
%              Depth                    :   29
%              Number of atoms          : 1721 (124217 expanded)
%              Number of equality atoms :   50 (3412 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t88_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                          = D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                 => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                            = D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                   => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('16',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','19','24','25'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['5','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('52',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['50','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('61',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','60','61','64'])).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','68'])).

thf('70',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','67'])).

thf('72',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('77',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','80'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','67'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t86_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ( X31 != X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('88',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('91',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('101',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','101','102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('108',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('110',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('113',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('119',plain,(
    ! [X17: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('120',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('122',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('123',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('125',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('126',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( m1_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['124','128'])).

thf('130',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('134',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('136',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['129','134','135'])).

thf('137',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['115','116','117','123','136'])).

thf('138',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['129','134','135'])).

thf('139',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['139','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('145',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('147',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('148',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','137','138','145','146','147','148','149','150'])).

thf('152',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    $false ),
    inference(demod,[status(thm)],['0','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UmdMtcG3HY
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/1.02  % Solved by: fo/fo7.sh
% 0.75/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/1.02  % done 1029 iterations in 0.564s
% 0.75/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/1.02  % SZS output start Refutation
% 0.75/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/1.02  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.75/1.02  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.75/1.02  thf(sk_E_type, type, sk_E: $i).
% 0.75/1.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/1.02  thf(sk_D_type, type, sk_D: $i).
% 0.75/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.75/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.75/1.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/1.02  thf(sk_G_type, type, sk_G: $i).
% 0.75/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.75/1.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/1.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/1.02  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.75/1.02  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.75/1.02  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.75/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/1.02  thf(sk_F_type, type, sk_F: $i).
% 0.75/1.02  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.75/1.02  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.75/1.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/1.02  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.75/1.02  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.75/1.02  thf(t88_tmap_1, conjecture,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.02       ( ![B:$i]:
% 0.75/1.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.75/1.02             ( l1_pre_topc @ B ) ) =>
% 0.75/1.02           ( ![C:$i]:
% 0.75/1.02             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.75/1.02               ( ![D:$i]:
% 0.75/1.02                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.75/1.02                   ( ![E:$i]:
% 0.75/1.02                     ( ( ( v1_funct_1 @ E ) & 
% 0.75/1.02                         ( v1_funct_2 @
% 0.75/1.02                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/1.02                         ( m1_subset_1 @
% 0.75/1.02                           E @ 
% 0.75/1.02                           ( k1_zfmisc_1 @
% 0.75/1.02                             ( k2_zfmisc_1 @
% 0.75/1.02                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/1.02                       ( ( ( g1_pre_topc @
% 0.75/1.02                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.75/1.02                           ( D ) ) =>
% 0.75/1.02                         ( ![F:$i]:
% 0.75/1.02                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.75/1.02                             ( ![G:$i]:
% 0.75/1.02                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.75/1.02                                 ( ( ( ( F ) = ( G ) ) & 
% 0.75/1.02                                     ( r1_tmap_1 @
% 0.75/1.02                                       C @ B @ 
% 0.75/1.02                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.75/1.02                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.75/1.02    (~( ![A:$i]:
% 0.75/1.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/1.02            ( l1_pre_topc @ A ) ) =>
% 0.75/1.02          ( ![B:$i]:
% 0.75/1.02            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.75/1.02                ( l1_pre_topc @ B ) ) =>
% 0.75/1.02              ( ![C:$i]:
% 0.75/1.02                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.75/1.02                  ( ![D:$i]:
% 0.75/1.02                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.75/1.02                      ( ![E:$i]:
% 0.75/1.02                        ( ( ( v1_funct_1 @ E ) & 
% 0.75/1.02                            ( v1_funct_2 @
% 0.75/1.02                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/1.02                            ( m1_subset_1 @
% 0.75/1.02                              E @ 
% 0.75/1.02                              ( k1_zfmisc_1 @
% 0.75/1.02                                ( k2_zfmisc_1 @
% 0.75/1.02                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/1.02                          ( ( ( g1_pre_topc @
% 0.75/1.02                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.75/1.02                              ( D ) ) =>
% 0.75/1.02                            ( ![F:$i]:
% 0.75/1.02                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.75/1.02                                ( ![G:$i]:
% 0.75/1.02                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.75/1.02                                    ( ( ( ( F ) = ( G ) ) & 
% 0.75/1.02                                        ( r1_tmap_1 @
% 0.75/1.02                                          C @ B @ 
% 0.75/1.02                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.75/1.02                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.75/1.02    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.75/1.02  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('1', plain,
% 0.75/1.02      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.75/1.02        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('2', plain, (((sk_F) = (sk_G))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('3', plain,
% 0.75/1.02      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.75/1.02        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.75/1.02      inference('demod', [status(thm)], ['1', '2'])).
% 0.75/1.02  thf('4', plain,
% 0.75/1.02      ((m1_subset_1 @ sk_E @ 
% 0.75/1.02        (k1_zfmisc_1 @ 
% 0.75/1.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf(fc10_tops_1, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.02       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.75/1.02  thf('5', plain,
% 0.75/1.02      (![X17 : $i]:
% 0.75/1.02         ((v3_pre_topc @ (k2_struct_0 @ X17) @ X17)
% 0.75/1.02          | ~ (l1_pre_topc @ X17)
% 0.75/1.02          | ~ (v2_pre_topc @ X17))),
% 0.75/1.02      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.75/1.02  thf(d3_struct_0, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.75/1.02  thf('6', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf(d10_xboole_0, axiom,
% 0.75/1.02    (![A:$i,B:$i]:
% 0.75/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/1.02  thf('7', plain,
% 0.75/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.75/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/1.02  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/1.02      inference('simplify', [status(thm)], ['7'])).
% 0.75/1.02  thf(t3_subset, axiom,
% 0.75/1.02    (![A:$i,B:$i]:
% 0.75/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/1.02  thf('9', plain,
% 0.75/1.02      (![X3 : $i, X5 : $i]:
% 0.75/1.02         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.75/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/1.02  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/1.02  thf('11', plain,
% 0.75/1.02      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf(t60_pre_topc, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.02       ( ![B:$i]:
% 0.75/1.02         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.75/1.02             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.75/1.02           ( ( v3_pre_topc @
% 0.75/1.02               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.75/1.02             ( m1_subset_1 @
% 0.75/1.02               B @ 
% 0.75/1.02               ( k1_zfmisc_1 @
% 0.75/1.02                 ( u1_struct_0 @
% 0.75/1.02                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.75/1.02  thf('12', plain,
% 0.75/1.02      (![X12 : $i, X13 : $i]:
% 0.75/1.02         (~ (v3_pre_topc @ X12 @ 
% 0.75/1.02             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.75/1.02          | ~ (m1_subset_1 @ X12 @ 
% 0.75/1.02               (k1_zfmisc_1 @ 
% 0.75/1.02                (u1_struct_0 @ 
% 0.75/1.02                 (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))))
% 0.75/1.02          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.75/1.02          | ~ (l1_pre_topc @ X13)
% 0.75/1.02          | ~ (v2_pre_topc @ X13))),
% 0.75/1.02      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.75/1.02  thf('13', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.75/1.02          | ~ (v2_pre_topc @ sk_C)
% 0.75/1.02          | ~ (l1_pre_topc @ sk_C)
% 0.75/1.02          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.75/1.02          | ~ (v3_pre_topc @ X0 @ 
% 0.75/1.02               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.75/1.02      inference('sup-', [status(thm)], ['11', '12'])).
% 0.75/1.02  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf(cc1_pre_topc, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.02       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.75/1.02  thf('15', plain,
% 0.75/1.02      (![X6 : $i, X7 : $i]:
% 0.75/1.02         (~ (m1_pre_topc @ X6 @ X7)
% 0.75/1.02          | (v2_pre_topc @ X6)
% 0.75/1.02          | ~ (l1_pre_topc @ X7)
% 0.75/1.02          | ~ (v2_pre_topc @ X7))),
% 0.75/1.02      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.75/1.02  thf('16', plain,
% 0.75/1.02      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.75/1.02      inference('sup-', [status(thm)], ['14', '15'])).
% 0.75/1.02  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('19', plain, ((v2_pre_topc @ sk_C)),
% 0.75/1.02      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.75/1.02  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf(dt_m1_pre_topc, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( l1_pre_topc @ A ) =>
% 0.75/1.02       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.75/1.02  thf('21', plain,
% 0.75/1.02      (![X10 : $i, X11 : $i]:
% 0.75/1.02         (~ (m1_pre_topc @ X10 @ X11)
% 0.75/1.02          | (l1_pre_topc @ X10)
% 0.75/1.02          | ~ (l1_pre_topc @ X11))),
% 0.75/1.02      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.75/1.02  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.75/1.02      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/1.02  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.75/1.02      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/1.02  thf('25', plain,
% 0.75/1.02      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('26', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.75/1.02          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.75/1.02          | ~ (v3_pre_topc @ X0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['13', '19', '24', '25'])).
% 0.75/1.02  thf('27', plain,
% 0.75/1.02      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.75/1.02        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.75/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.75/1.02      inference('sup-', [status(thm)], ['10', '26'])).
% 0.75/1.02  thf('28', plain,
% 0.75/1.02      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.75/1.02        | ~ (l1_struct_0 @ sk_D)
% 0.75/1.02        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.75/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.75/1.02      inference('sup-', [status(thm)], ['6', '27'])).
% 0.75/1.02  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('30', plain,
% 0.75/1.02      (![X10 : $i, X11 : $i]:
% 0.75/1.02         (~ (m1_pre_topc @ X10 @ X11)
% 0.75/1.02          | (l1_pre_topc @ X10)
% 0.75/1.02          | ~ (l1_pre_topc @ X11))),
% 0.75/1.02      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.75/1.02  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.75/1.02      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/1.02  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['31', '32'])).
% 0.75/1.02  thf(dt_l1_pre_topc, axiom,
% 0.75/1.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.75/1.02  thf('34', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.75/1.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/1.02  thf('35', plain, ((l1_struct_0 @ sk_D)),
% 0.75/1.02      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/1.02  thf('36', plain,
% 0.75/1.02      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.75/1.02        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.75/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.75/1.02      inference('demod', [status(thm)], ['28', '35'])).
% 0.75/1.02  thf('37', plain,
% 0.75/1.02      ((~ (v2_pre_topc @ sk_D)
% 0.75/1.02        | ~ (l1_pre_topc @ sk_D)
% 0.75/1.02        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.75/1.02           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.75/1.02      inference('sup-', [status(thm)], ['5', '36'])).
% 0.75/1.02  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('39', plain,
% 0.75/1.02      (![X6 : $i, X7 : $i]:
% 0.75/1.02         (~ (m1_pre_topc @ X6 @ X7)
% 0.75/1.02          | (v2_pre_topc @ X6)
% 0.75/1.02          | ~ (l1_pre_topc @ X7)
% 0.75/1.02          | ~ (v2_pre_topc @ X7))),
% 0.75/1.02      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.75/1.02  thf('40', plain,
% 0.75/1.02      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.75/1.02      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/1.02  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('43', plain, ((v2_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.75/1.02  thf('44', plain, ((l1_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['31', '32'])).
% 0.75/1.02  thf('45', plain,
% 0.75/1.02      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.75/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.75/1.02      inference('demod', [status(thm)], ['37', '43', '44'])).
% 0.75/1.02  thf('46', plain,
% 0.75/1.02      (![X3 : $i, X4 : $i]:
% 0.75/1.02         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.75/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/1.02  thf('47', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.75/1.02      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/1.02  thf('48', plain,
% 0.75/1.02      (![X0 : $i, X2 : $i]:
% 0.75/1.02         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/1.02  thf('49', plain,
% 0.75/1.02      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.75/1.02        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.75/1.02      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/1.02  thf('50', plain,
% 0.75/1.02      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('51', plain,
% 0.75/1.02      (![X17 : $i]:
% 0.75/1.02         ((v3_pre_topc @ (k2_struct_0 @ X17) @ X17)
% 0.75/1.02          | ~ (l1_pre_topc @ X17)
% 0.75/1.02          | ~ (v2_pre_topc @ X17))),
% 0.75/1.02      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.75/1.02  thf('52', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf('53', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/1.02  thf('54', plain,
% 0.75/1.02      (![X13 : $i, X14 : $i]:
% 0.75/1.02         (~ (v3_pre_topc @ X14 @ X13)
% 0.75/1.02          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.75/1.02          | (m1_subset_1 @ X14 @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (u1_struct_0 @ 
% 0.75/1.02               (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))))
% 0.75/1.02          | ~ (l1_pre_topc @ X13)
% 0.75/1.02          | ~ (v2_pre_topc @ X13))),
% 0.75/1.02      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.75/1.02  thf('55', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (u1_struct_0 @ 
% 0.75/1.02               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.75/1.02          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/1.02  thf('56', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.75/1.02          | ~ (l1_struct_0 @ X0)
% 0.75/1.02          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (u1_struct_0 @ 
% 0.75/1.02               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['52', '55'])).
% 0.75/1.02  thf('57', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (u1_struct_0 @ 
% 0.75/1.02               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.75/1.02          | ~ (l1_struct_0 @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['51', '56'])).
% 0.75/1.02  thf('58', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (l1_struct_0 @ X0)
% 0.75/1.02          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (u1_struct_0 @ 
% 0.75/1.02               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0))),
% 0.75/1.02      inference('simplify', [status(thm)], ['57'])).
% 0.75/1.02  thf('59', plain,
% 0.75/1.02      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.75/1.02         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.75/1.02        | ~ (v2_pre_topc @ sk_C)
% 0.75/1.02        | ~ (l1_pre_topc @ sk_C)
% 0.75/1.02        | ~ (l1_struct_0 @ sk_C))),
% 0.75/1.02      inference('sup+', [status(thm)], ['50', '58'])).
% 0.75/1.02  thf('60', plain, ((v2_pre_topc @ sk_C)),
% 0.75/1.02      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.75/1.02  thf('61', plain, ((l1_pre_topc @ sk_C)),
% 0.75/1.02      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/1.02  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 0.75/1.02      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/1.02  thf('63', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.75/1.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/1.02  thf('64', plain, ((l1_struct_0 @ sk_C)),
% 0.75/1.02      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/1.02  thf('65', plain,
% 0.75/1.02      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.75/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.75/1.02      inference('demod', [status(thm)], ['59', '60', '61', '64'])).
% 0.75/1.02  thf('66', plain,
% 0.75/1.02      (![X3 : $i, X4 : $i]:
% 0.75/1.02         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.75/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/1.02  thf('67', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/1.02  thf('68', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['49', '67'])).
% 0.75/1.02  thf('69', plain,
% 0.75/1.02      ((m1_subset_1 @ sk_E @ 
% 0.75/1.02        (k1_zfmisc_1 @ 
% 0.75/1.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.75/1.02      inference('demod', [status(thm)], ['4', '68'])).
% 0.75/1.02  thf('70', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf('71', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['49', '67'])).
% 0.75/1.02  thf('72', plain,
% 0.75/1.02      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.75/1.02      inference('sup+', [status(thm)], ['70', '71'])).
% 0.75/1.02  thf('73', plain, ((l1_struct_0 @ sk_D)),
% 0.75/1.02      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/1.02  thf('74', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/1.02  thf('75', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf('76', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/1.02  thf('77', plain,
% 0.75/1.02      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.75/1.02      inference('sup+', [status(thm)], ['75', '76'])).
% 0.75/1.02  thf('78', plain, ((l1_struct_0 @ sk_C)),
% 0.75/1.02      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/1.02  thf('79', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['77', '78'])).
% 0.75/1.02  thf('80', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['74', '79'])).
% 0.75/1.02  thf('81', plain,
% 0.75/1.02      ((m1_subset_1 @ sk_E @ 
% 0.75/1.02        (k1_zfmisc_1 @ 
% 0.75/1.02         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.75/1.02      inference('demod', [status(thm)], ['69', '80'])).
% 0.75/1.02  thf('82', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['49', '67'])).
% 0.75/1.02  thf('83', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/1.02  thf('84', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['82', '83'])).
% 0.75/1.02  thf('85', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['77', '78'])).
% 0.75/1.02  thf('86', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['84', '85'])).
% 0.75/1.02  thf(t86_tmap_1, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.02       ( ![B:$i]:
% 0.75/1.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.75/1.02             ( l1_pre_topc @ B ) ) =>
% 0.75/1.02           ( ![C:$i]:
% 0.75/1.02             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.75/1.02               ( ![D:$i]:
% 0.75/1.02                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.75/1.02                   ( ![E:$i]:
% 0.75/1.02                     ( ( ( v1_funct_1 @ E ) & 
% 0.75/1.02                         ( v1_funct_2 @
% 0.75/1.02                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/1.02                         ( m1_subset_1 @
% 0.75/1.02                           E @ 
% 0.75/1.02                           ( k1_zfmisc_1 @
% 0.75/1.02                             ( k2_zfmisc_1 @
% 0.75/1.02                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/1.02                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.75/1.02                         ( ![F:$i]:
% 0.75/1.02                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.75/1.02                             ( ![G:$i]:
% 0.75/1.02                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.75/1.02                                 ( ( ( F ) = ( G ) ) =>
% 0.75/1.02                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.75/1.02                                     ( r1_tmap_1 @
% 0.75/1.02                                       C @ B @ 
% 0.75/1.02                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/1.02  thf('87', plain,
% 0.75/1.02      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.75/1.02         ((v2_struct_0 @ X27)
% 0.75/1.02          | ~ (v2_pre_topc @ X27)
% 0.75/1.02          | ~ (l1_pre_topc @ X27)
% 0.75/1.02          | (v2_struct_0 @ X28)
% 0.75/1.02          | ~ (m1_pre_topc @ X28 @ X29)
% 0.75/1.02          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.75/1.02          | ~ (m1_pre_topc @ X30 @ X28)
% 0.75/1.02          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 0.75/1.02          | ((X31) != (X32))
% 0.75/1.02          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.75/1.02               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.75/1.02          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X31)
% 0.75/1.02          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.75/1.02          | ~ (m1_subset_1 @ X33 @ 
% 0.75/1.02               (k1_zfmisc_1 @ 
% 0.75/1.02                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.75/1.02          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.75/1.02          | ~ (v1_funct_1 @ X33)
% 0.75/1.02          | ~ (m1_pre_topc @ X30 @ X29)
% 0.75/1.02          | (v2_struct_0 @ X30)
% 0.75/1.02          | ~ (l1_pre_topc @ X29)
% 0.75/1.02          | ~ (v2_pre_topc @ X29)
% 0.75/1.02          | (v2_struct_0 @ X29))),
% 0.75/1.02      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.75/1.02  thf('88', plain,
% 0.75/1.02      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 0.75/1.02         ((v2_struct_0 @ X29)
% 0.75/1.02          | ~ (v2_pre_topc @ X29)
% 0.75/1.02          | ~ (l1_pre_topc @ X29)
% 0.75/1.02          | (v2_struct_0 @ X30)
% 0.75/1.02          | ~ (m1_pre_topc @ X30 @ X29)
% 0.75/1.02          | ~ (v1_funct_1 @ X33)
% 0.75/1.02          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.75/1.02          | ~ (m1_subset_1 @ X33 @ 
% 0.75/1.02               (k1_zfmisc_1 @ 
% 0.75/1.02                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.75/1.02          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.75/1.02          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 0.75/1.02          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.75/1.02               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.75/1.02          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.75/1.02          | ~ (m1_pre_topc @ X30 @ X28)
% 0.75/1.02          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.75/1.02          | ~ (m1_pre_topc @ X28 @ X29)
% 0.75/1.02          | (v2_struct_0 @ X28)
% 0.75/1.02          | ~ (l1_pre_topc @ X27)
% 0.75/1.02          | ~ (v2_pre_topc @ X27)
% 0.75/1.02          | (v2_struct_0 @ X27))),
% 0.75/1.02      inference('simplify', [status(thm)], ['87'])).
% 0.75/1.02  thf('89', plain,
% 0.75/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/1.02         (~ (m1_subset_1 @ X1 @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.75/1.02          | (v2_struct_0 @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (v2_struct_0 @ sk_D)
% 0.75/1.02          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.75/1.02          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.75/1.02          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.75/1.02          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 0.75/1.02          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.75/1.02               X4)
% 0.75/1.02          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.75/1.02          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.75/1.02          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.75/1.02          | ~ (v1_funct_1 @ X1)
% 0.75/1.02          | ~ (m1_pre_topc @ X3 @ X2)
% 0.75/1.02          | (v2_struct_0 @ X3)
% 0.75/1.02          | ~ (l1_pre_topc @ X2)
% 0.75/1.02          | ~ (v2_pre_topc @ X2)
% 0.75/1.02          | (v2_struct_0 @ X2))),
% 0.75/1.02      inference('sup-', [status(thm)], ['86', '88'])).
% 0.75/1.02  thf('90', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['84', '85'])).
% 0.75/1.02  thf('91', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['84', '85'])).
% 0.75/1.02  thf('92', plain,
% 0.75/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/1.02         (~ (m1_subset_1 @ X1 @ 
% 0.75/1.02             (k1_zfmisc_1 @ 
% 0.75/1.02              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.75/1.02          | (v2_struct_0 @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (v2_struct_0 @ sk_D)
% 0.75/1.02          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.75/1.02          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.75/1.02          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.75/1.02          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 0.75/1.02          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.75/1.02               X4)
% 0.75/1.02          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.75/1.02          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.75/1.02          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.75/1.02          | ~ (v1_funct_1 @ X1)
% 0.75/1.02          | ~ (m1_pre_topc @ X3 @ X2)
% 0.75/1.02          | (v2_struct_0 @ X3)
% 0.75/1.02          | ~ (l1_pre_topc @ X2)
% 0.75/1.02          | ~ (v2_pre_topc @ X2)
% 0.75/1.02          | (v2_struct_0 @ X2))),
% 0.75/1.02      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.75/1.02  thf('93', plain,
% 0.75/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.02         ((v2_struct_0 @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (v2_struct_0 @ X1)
% 0.75/1.02          | ~ (m1_pre_topc @ X1 @ X0)
% 0.75/1.02          | ~ (v1_funct_1 @ sk_E)
% 0.75/1.02          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.75/1.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.75/1.02          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.75/1.02          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.75/1.02               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.75/1.02          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.75/1.02          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.75/1.02          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.75/1.02          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.75/1.02          | (v2_struct_0 @ sk_D)
% 0.75/1.02          | ~ (l1_pre_topc @ sk_B)
% 0.75/1.02          | ~ (v2_pre_topc @ sk_B)
% 0.75/1.02          | (v2_struct_0 @ sk_B))),
% 0.75/1.02      inference('sup-', [status(thm)], ['81', '92'])).
% 0.75/1.02  thf('94', plain, ((v1_funct_1 @ sk_E)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('95', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf('96', plain,
% 0.75/1.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('97', plain,
% 0.75/1.02      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.75/1.02        | ~ (l1_struct_0 @ sk_D))),
% 0.75/1.02      inference('sup+', [status(thm)], ['95', '96'])).
% 0.75/1.02  thf('98', plain, ((l1_struct_0 @ sk_D)),
% 0.75/1.02      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/1.02  thf('99', plain,
% 0.75/1.02      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.75/1.02      inference('demod', [status(thm)], ['97', '98'])).
% 0.75/1.02  thf('100', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['77', '78'])).
% 0.75/1.02  thf('101', plain,
% 0.75/1.02      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.75/1.02      inference('demod', [status(thm)], ['99', '100'])).
% 0.75/1.02  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('104', plain,
% 0.75/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.02         ((v2_struct_0 @ X0)
% 0.75/1.02          | ~ (v2_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (v2_struct_0 @ X1)
% 0.75/1.02          | ~ (m1_pre_topc @ X1 @ X0)
% 0.75/1.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.75/1.02          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.75/1.02          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.75/1.02               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.75/1.02          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.75/1.02          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.75/1.02          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.75/1.02          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.75/1.02          | (v2_struct_0 @ sk_D)
% 0.75/1.02          | (v2_struct_0 @ sk_B))),
% 0.75/1.02      inference('demod', [status(thm)], ['93', '94', '101', '102', '103'])).
% 0.75/1.02  thf('105', plain,
% 0.75/1.02      (((v2_struct_0 @ sk_B)
% 0.75/1.02        | (v2_struct_0 @ sk_D)
% 0.75/1.02        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.75/1.02        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.75/1.02        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.75/1.02        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.75/1.02        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.75/1.02        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.75/1.02        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.75/1.02        | (v2_struct_0 @ sk_C)
% 0.75/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.75/1.02        | ~ (v2_pre_topc @ sk_A)
% 0.75/1.02        | (v2_struct_0 @ sk_A))),
% 0.75/1.02      inference('sup-', [status(thm)], ['3', '104'])).
% 0.75/1.02  thf('106', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('107', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['74', '79'])).
% 0.75/1.02  thf('108', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['84', '85'])).
% 0.75/1.02  thf(t16_tsep_1, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.02       ( ![B:$i]:
% 0.75/1.02         ( ( m1_pre_topc @ B @ A ) =>
% 0.75/1.02           ( ![C:$i]:
% 0.75/1.02             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.02               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.75/1.02                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.75/1.02                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.75/1.02  thf('109', plain,
% 0.75/1.02      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.75/1.02         (~ (m1_pre_topc @ X18 @ X19)
% 0.75/1.02          | ((X20) != (u1_struct_0 @ X18))
% 0.75/1.02          | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.02          | (v1_tsep_1 @ X18 @ X19)
% 0.75/1.02          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.02          | ~ (l1_pre_topc @ X19)
% 0.75/1.02          | ~ (v2_pre_topc @ X19))),
% 0.75/1.02      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.75/1.02  thf('110', plain,
% 0.75/1.02      (![X18 : $i, X19 : $i]:
% 0.75/1.02         (~ (v2_pre_topc @ X19)
% 0.75/1.02          | ~ (l1_pre_topc @ X19)
% 0.75/1.02          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.75/1.02               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.02          | (v1_tsep_1 @ X18 @ X19)
% 0.75/1.02          | ~ (v3_pre_topc @ (u1_struct_0 @ X18) @ X19)
% 0.75/1.02          | ~ (m1_pre_topc @ X18 @ X19))),
% 0.75/1.02      inference('simplify', [status(thm)], ['109'])).
% 0.75/1.02  thf('111', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.75/1.02             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.75/1.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.75/1.02          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.75/1.02          | (v1_tsep_1 @ X0 @ sk_D)
% 0.75/1.02          | ~ (l1_pre_topc @ sk_D)
% 0.75/1.02          | ~ (v2_pre_topc @ sk_D))),
% 0.75/1.02      inference('sup-', [status(thm)], ['108', '110'])).
% 0.75/1.02  thf('112', plain, ((l1_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['31', '32'])).
% 0.75/1.02  thf('113', plain, ((v2_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.75/1.02  thf('114', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.75/1.02             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.75/1.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.75/1.02          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.75/1.02          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.75/1.02  thf('115', plain,
% 0.75/1.02      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.75/1.02           (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.75/1.02        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.75/1.02        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.75/1.02        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 0.75/1.02      inference('sup-', [status(thm)], ['107', '114'])).
% 0.75/1.02  thf('116', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/1.02  thf('117', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['74', '79'])).
% 0.75/1.02  thf('118', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['77', '78'])).
% 0.75/1.02  thf('119', plain,
% 0.75/1.02      (![X17 : $i]:
% 0.75/1.02         ((v3_pre_topc @ (k2_struct_0 @ X17) @ X17)
% 0.75/1.02          | ~ (l1_pre_topc @ X17)
% 0.75/1.02          | ~ (v2_pre_topc @ X17))),
% 0.75/1.02      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.75/1.02  thf('120', plain,
% 0.75/1.02      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.75/1.02        | ~ (v2_pre_topc @ sk_D)
% 0.75/1.02        | ~ (l1_pre_topc @ sk_D))),
% 0.75/1.02      inference('sup+', [status(thm)], ['118', '119'])).
% 0.75/1.02  thf('121', plain, ((v2_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.75/1.02  thf('122', plain, ((l1_pre_topc @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['31', '32'])).
% 0.75/1.02  thf('123', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.75/1.02  thf('124', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['74', '79'])).
% 0.75/1.02  thf(t2_tsep_1, axiom,
% 0.75/1.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.75/1.02  thf('125', plain,
% 0.75/1.02      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.75/1.02      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.75/1.02  thf(t65_pre_topc, axiom,
% 0.75/1.02    (![A:$i]:
% 0.75/1.02     ( ( l1_pre_topc @ A ) =>
% 0.75/1.02       ( ![B:$i]:
% 0.75/1.02         ( ( l1_pre_topc @ B ) =>
% 0.75/1.02           ( ( m1_pre_topc @ A @ B ) <=>
% 0.75/1.02             ( m1_pre_topc @
% 0.75/1.02               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.75/1.02  thf('126', plain,
% 0.75/1.02      (![X15 : $i, X16 : $i]:
% 0.75/1.02         (~ (l1_pre_topc @ X15)
% 0.75/1.02          | ~ (m1_pre_topc @ X16 @ X15)
% 0.75/1.02          | (m1_pre_topc @ X16 @ 
% 0.75/1.02             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.75/1.02          | ~ (l1_pre_topc @ X16))),
% 0.75/1.02      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.75/1.02  thf('127', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         (~ (l1_pre_topc @ X0)
% 0.75/1.02          | ~ (l1_pre_topc @ X0)
% 0.75/1.02          | (m1_pre_topc @ X0 @ 
% 0.75/1.02             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/1.02          | ~ (l1_pre_topc @ X0))),
% 0.75/1.02      inference('sup-', [status(thm)], ['125', '126'])).
% 0.75/1.02  thf('128', plain,
% 0.75/1.02      (![X0 : $i]:
% 0.75/1.02         ((m1_pre_topc @ X0 @ 
% 0.75/1.02           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.75/1.02          | ~ (l1_pre_topc @ X0))),
% 0.75/1.02      inference('simplify', [status(thm)], ['127'])).
% 0.75/1.02  thf('129', plain,
% 0.75/1.02      (((m1_pre_topc @ sk_C @ 
% 0.75/1.02         (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.75/1.02        | ~ (l1_pre_topc @ sk_C))),
% 0.75/1.02      inference('sup+', [status(thm)], ['124', '128'])).
% 0.75/1.02  thf('130', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf('131', plain,
% 0.75/1.02      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('132', plain,
% 0.75/1.02      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 0.75/1.02        | ~ (l1_struct_0 @ sk_C))),
% 0.75/1.02      inference('sup+', [status(thm)], ['130', '131'])).
% 0.75/1.02  thf('133', plain, ((l1_struct_0 @ sk_C)),
% 0.75/1.02      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/1.02  thf('134', plain,
% 0.75/1.02      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.75/1.02      inference('demod', [status(thm)], ['132', '133'])).
% 0.75/1.02  thf('135', plain, ((l1_pre_topc @ sk_C)),
% 0.75/1.02      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/1.02  thf('136', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['129', '134', '135'])).
% 0.75/1.02  thf('137', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['115', '116', '117', '123', '136'])).
% 0.75/1.02  thf('138', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.75/1.02      inference('demod', [status(thm)], ['129', '134', '135'])).
% 0.75/1.02  thf('139', plain,
% 0.75/1.02      (![X8 : $i]:
% 0.75/1.02         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.75/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/1.02  thf('140', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('141', plain, (((sk_F) = (sk_G))),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('142', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['140', '141'])).
% 0.75/1.02  thf('143', plain,
% 0.75/1.02      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.75/1.02      inference('sup+', [status(thm)], ['139', '142'])).
% 0.75/1.02  thf('144', plain, ((l1_struct_0 @ sk_C)),
% 0.75/1.02      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/1.02  thf('145', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['143', '144'])).
% 0.75/1.02  thf('146', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['74', '79'])).
% 0.75/1.02  thf('147', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.75/1.02      inference('demod', [status(thm)], ['143', '144'])).
% 0.75/1.02  thf('148', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('151', plain,
% 0.75/1.02      (((v2_struct_0 @ sk_B)
% 0.75/1.02        | (v2_struct_0 @ sk_D)
% 0.75/1.02        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.75/1.02        | (v2_struct_0 @ sk_C)
% 0.75/1.02        | (v2_struct_0 @ sk_A))),
% 0.75/1.02      inference('demod', [status(thm)],
% 0.75/1.02                ['105', '106', '137', '138', '145', '146', '147', '148', 
% 0.75/1.02                 '149', '150'])).
% 0.75/1.02  thf('152', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('153', plain,
% 0.75/1.02      (((v2_struct_0 @ sk_A)
% 0.75/1.02        | (v2_struct_0 @ sk_C)
% 0.75/1.02        | (v2_struct_0 @ sk_D)
% 0.75/1.02        | (v2_struct_0 @ sk_B))),
% 0.75/1.02      inference('sup-', [status(thm)], ['151', '152'])).
% 0.75/1.02  thf('154', plain, (~ (v2_struct_0 @ sk_D)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('155', plain,
% 0.75/1.02      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.75/1.02      inference('sup-', [status(thm)], ['153', '154'])).
% 0.75/1.02  thf('156', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('157', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.75/1.02      inference('clc', [status(thm)], ['155', '156'])).
% 0.75/1.02  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.02  thf('159', plain, ((v2_struct_0 @ sk_C)),
% 0.75/1.02      inference('clc', [status(thm)], ['157', '158'])).
% 0.75/1.02  thf('160', plain, ($false), inference('demod', [status(thm)], ['0', '159'])).
% 0.75/1.02  
% 0.75/1.02  % SZS output end Refutation
% 0.75/1.02  
% 0.75/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
