%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2drzx0J5F

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 942 expanded)
%              Number of leaves         :   38 ( 287 expanded)
%              Depth                    :   29
%              Number of atoms          : 2148 (28883 expanded)
%              Number of equality atoms :   52 ( 773 expanded)
%              Maximal formula depth    :   30 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( ( k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) @ X13 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('20',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('42',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','38','39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('53',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('57',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('69',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ sk_F ),
    inference(demod,[status(thm)],['3','78'])).

thf('80',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('81',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('88',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('90',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('94',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('96',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('103',plain,
    ( ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','71'])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ( X29 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ ( k3_tmap_1 @ X26 @ X31 @ X27 @ X28 @ X32 ) @ X30 )
      | ( r1_tmap_1 @ X27 @ X31 @ X32 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t87_tmap_1])).

thf('112',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X27 @ X31 @ X32 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ ( k3_tmap_1 @ X26 @ X31 @ X27 @ X28 @ X32 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( v1_tsep_1 @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','118'])).

thf('120',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('121',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('122',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('129',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['127','128'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('131',plain,(
    ! [X8: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('132',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('134',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

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

thf('137',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('138',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('146',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('147',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('148',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('150',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('151',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['119','120','129','148','149','150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_D ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['154','157','158'])).

thf('160',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['0','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2drzx0J5F
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 359 iterations in 0.131s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.58  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.58  thf(t88_tmap_1, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.58             ( l1_pre_topc @ B ) ) =>
% 0.20/0.58           ( ![C:$i]:
% 0.20/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.58               ( ![D:$i]:
% 0.20/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.58                   ( ![E:$i]:
% 0.20/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.58                         ( v1_funct_2 @
% 0.20/0.58                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.58                         ( m1_subset_1 @
% 0.20/0.58                           E @ 
% 0.20/0.58                           ( k1_zfmisc_1 @
% 0.20/0.58                             ( k2_zfmisc_1 @
% 0.20/0.58                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.58                       ( ( ( g1_pre_topc @
% 0.20/0.58                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.20/0.58                           ( D ) ) =>
% 0.20/0.58                         ( ![F:$i]:
% 0.20/0.58                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.58                             ( ![G:$i]:
% 0.20/0.58                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.58                                 ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.58                                     ( r1_tmap_1 @
% 0.20/0.58                                       C @ B @ 
% 0.20/0.58                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.20/0.58                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.58            ( l1_pre_topc @ A ) ) =>
% 0.20/0.58          ( ![B:$i]:
% 0.20/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.58                ( l1_pre_topc @ B ) ) =>
% 0.20/0.58              ( ![C:$i]:
% 0.20/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.58                  ( ![D:$i]:
% 0.20/0.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.58                      ( ![E:$i]:
% 0.20/0.58                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.58                            ( v1_funct_2 @
% 0.20/0.58                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.58                            ( m1_subset_1 @
% 0.20/0.58                              E @ 
% 0.20/0.58                              ( k1_zfmisc_1 @
% 0.20/0.58                                ( k2_zfmisc_1 @
% 0.20/0.58                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.58                          ( ( ( g1_pre_topc @
% 0.20/0.58                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.20/0.58                              ( D ) ) =>
% 0.20/0.58                            ( ![F:$i]:
% 0.20/0.58                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.58                                ( ![G:$i]:
% 0.20/0.58                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.58                                    ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.58                                        ( r1_tmap_1 @
% 0.20/0.58                                          C @ B @ 
% 0.20/0.58                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.20/0.58                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.20/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.58        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('2', plain, (((sk_F) = (sk_G))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.58        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.20/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('5', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_E @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(d5_tmap_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.58             ( l1_pre_topc @ B ) ) =>
% 0.20/0.58           ( ![C:$i]:
% 0.20/0.58             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.58               ( ![D:$i]:
% 0.20/0.58                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.58                   ( ![E:$i]:
% 0.20/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.58                         ( v1_funct_2 @
% 0.20/0.58                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.58                         ( m1_subset_1 @
% 0.20/0.58                           E @ 
% 0.20/0.58                           ( k1_zfmisc_1 @
% 0.20/0.58                             ( k2_zfmisc_1 @
% 0.20/0.58                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.58                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.58                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.58                           ( k2_partfun1 @
% 0.20/0.58                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.58                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X9)
% 0.20/0.58          | ~ (v2_pre_topc @ X9)
% 0.20/0.58          | ~ (l1_pre_topc @ X9)
% 0.20/0.58          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.58          | ~ (m1_pre_topc @ X10 @ X12)
% 0.20/0.58          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 0.20/0.58                 X13 @ (u1_struct_0 @ X10)))
% 0.20/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.58               (k1_zfmisc_1 @ 
% 0.20/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 0.20/0.58          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 0.20/0.58          | ~ (v1_funct_1 @ X13)
% 0.20/0.58          | ~ (m1_pre_topc @ X12 @ X11)
% 0.20/0.58          | ~ (l1_pre_topc @ X11)
% 0.20/0.58          | ~ (v2_pre_topc @ X11)
% 0.20/0.58          | (v2_struct_0 @ X11))),
% 0.20/0.58      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X0)
% 0.20/0.58          | ~ (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.58          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.58          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.58          | (v2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.58  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X0)
% 0.20/0.58          | ~ (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.58          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.58          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.58          | (v2_struct_0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_struct_0 @ sk_B)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.58          | (v2_struct_0 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '13'])).
% 0.20/0.58  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_struct_0 @ sk_B)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.58          | (v2_struct_0 @ sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.58        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.58        | (v2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '17'])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t2_tsep_1, axiom,
% 0.20/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.58  thf(t65_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( l1_pre_topc @ B ) =>
% 0.20/0.58           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.58             ( m1_pre_topc @
% 0.20/0.58               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X6)
% 0.20/0.58          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.58          | (m1_pre_topc @ X7 @ 
% 0.20/0.58             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.58          | ~ (l1_pre_topc @ X7))),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | (m1_pre_topc @ X0 @ 
% 0.20/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.58          | ~ (l1_pre_topc @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((m1_pre_topc @ X0 @ 
% 0.20/0.58           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.58          | ~ (l1_pre_topc @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.58  thf('24', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.58      inference('sup+', [status(thm)], ['19', '23'])).
% 0.20/0.58  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(dt_m1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X4 : $i, X5 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.58  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.58  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((v2_struct_0 @ X0)
% 0.20/0.58          | ~ (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0)
% 0.20/0.58          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.58          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.58          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.58          | (v2_struct_0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ sk_D)
% 0.20/0.58          | (v2_struct_0 @ sk_B)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.58          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.58          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.58          | (v2_struct_0 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.58  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X4 : $i, X5 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.58  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('38', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.58          | (v2_pre_topc @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X1)
% 0.20/0.58          | ~ (v2_pre_topc @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.58  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('45', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_struct_0 @ sk_B)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.58          | (v2_struct_0 @ sk_D))),
% 0.20/0.58      inference('demod', [status(thm)], ['33', '38', '39', '45'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((v2_struct_0 @ sk_D)
% 0.20/0.58          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.58          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.58          | (v2_struct_0 @ sk_B))),
% 0.20/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_B)
% 0.20/0.58        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.58        | (v2_struct_0 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['30', '47'])).
% 0.20/0.58  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_D)
% 0.20/0.58        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.58      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.58  thf('51', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (u1_struct_0 @ sk_C)))),
% 0.20/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf(d3_struct_0, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      (![X2 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X2 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (![X2 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (u1_struct_0 @ sk_C)))),
% 0.20/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58          = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58             sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_D))),
% 0.20/0.58      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf('58', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf(dt_l1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.58  thf('59', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('60', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (u1_struct_0 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['57', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58          = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.58             sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['54', '61'])).
% 0.20/0.58  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('64', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (u1_struct_0 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['62', '65'])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58          = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.58             sk_E @ (k2_struct_0 @ sk_C)))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.58      inference('sup+', [status(thm)], ['53', '66'])).
% 0.20/0.58  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.58  thf('69', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('70', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (k2_struct_0 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['67', '70'])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (((k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58         (k2_struct_0 @ sk_C))
% 0.20/0.58         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (u1_struct_0 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['52', '71'])).
% 0.20/0.58  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_A)
% 0.20/0.58        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.58               sk_E @ (k2_struct_0 @ sk_C)))
% 0.20/0.58        | (v2_struct_0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['18', '72', '73'])).
% 0.20/0.58  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (((v2_struct_0 @ sk_B)
% 0.20/0.58        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.58               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.20/0.58      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.58  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('78', plain,
% 0.20/0.58      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.58         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58            (k2_struct_0 @ sk_C)))),
% 0.20/0.58      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.58  thf('79', plain,
% 0.20/0.58      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.58        (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.58         (k2_struct_0 @ sk_C)) @ 
% 0.20/0.58        sk_F)),
% 0.20/0.58      inference('demod', [status(thm)], ['3', '78'])).
% 0.20/0.58  thf('80', plain,
% 0.20/0.58      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.58  thf('81', plain,
% 0.20/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('82', plain,
% 0.20/0.58      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X6)
% 0.20/0.58          | ~ (m1_pre_topc @ X7 @ 
% 0.20/0.58               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.58          | (m1_pre_topc @ X7 @ X6)
% 0.20/0.58          | ~ (l1_pre_topc @ X7))),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.58  thf('84', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ 
% 0.20/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.58          | ~ (l1_pre_topc @ 
% 0.20/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.58          | (m1_pre_topc @ 
% 0.20/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X0)
% 0.20/0.58          | (m1_pre_topc @ 
% 0.20/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.20/0.58          | ~ (l1_pre_topc @ 
% 0.20/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.58        | (m1_pre_topc @ 
% 0.20/0.58           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.20/0.58        | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['81', '85'])).
% 0.20/0.58  thf('87', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('88', plain,
% 0.20/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('89', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.20/0.59  thf('91', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.59              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.59                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59          | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.59  thf('92', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_B)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.59              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.59                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.59          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.59          | (v2_struct_0 @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.59  thf('93', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('94', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('95', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.59          | (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X1)
% 0.20/0.59          | ~ (v2_pre_topc @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.59  thf('96', plain,
% 0.20/0.59      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.59  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('99', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.59  thf('100', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_B)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.59              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.59                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.59          | (v2_struct_0 @ sk_C))),
% 0.20/0.59      inference('demod', [status(thm)], ['92', '93', '99'])).
% 0.20/0.59  thf('101', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.59            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.59               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['80', '100'])).
% 0.20/0.59  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('103', plain,
% 0.20/0.59      (((k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.59         (k2_struct_0 @ sk_C))
% 0.20/0.59         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.59            (u1_struct_0 @ sk_C)))),
% 0.20/0.59      inference('demod', [status(thm)], ['52', '71'])).
% 0.20/0.59  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.59  thf('105', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_C)
% 0.20/0.59        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.59            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.59               sk_E @ (k2_struct_0 @ sk_C)))
% 0.20/0.59        | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.20/0.59  thf('106', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('107', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.59            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.59               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.20/0.59      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.59  thf('108', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('109', plain,
% 0.20/0.59      (((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.59         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.59            (k2_struct_0 @ sk_C)))),
% 0.20/0.59      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.59  thf('110', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t87_tmap_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59             ( l1_pre_topc @ B ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.59               ( ![D:$i]:
% 0.20/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.59                   ( ![E:$i]:
% 0.20/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                         ( v1_funct_2 @
% 0.20/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.59                         ( m1_subset_1 @
% 0.20/0.59                           E @ 
% 0.20/0.59                           ( k1_zfmisc_1 @
% 0.20/0.59                             ( k2_zfmisc_1 @
% 0.20/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.59                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.20/0.59                           ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.59                         ( ![F:$i]:
% 0.20/0.59                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.59                             ( ![G:$i]:
% 0.20/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.59                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.59                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.59                                     ( r1_tmap_1 @
% 0.20/0.59                                       C @ A @ 
% 0.20/0.59                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('111', plain,
% 0.20/0.59      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X26)
% 0.20/0.59          | ~ (v2_pre_topc @ X26)
% 0.20/0.59          | ~ (l1_pre_topc @ X26)
% 0.20/0.59          | (v2_struct_0 @ X27)
% 0.20/0.59          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.59          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.20/0.59          | ~ (m1_pre_topc @ X28 @ X26)
% 0.20/0.59          | ~ (m1_pre_topc @ X28 @ X27)
% 0.20/0.59          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.20/0.59          | ((X29) != (X30))
% 0.20/0.59          | ~ (r1_tmap_1 @ X28 @ X31 @ 
% 0.20/0.59               (k3_tmap_1 @ X26 @ X31 @ X27 @ X28 @ X32) @ X30)
% 0.20/0.59          | (r1_tmap_1 @ X27 @ X31 @ X32 @ X29)
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X31))))
% 0.20/0.59          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X31))
% 0.20/0.59          | ~ (v1_funct_1 @ X32)
% 0.20/0.59          | ~ (m1_pre_topc @ X28 @ X26)
% 0.20/0.59          | (v2_struct_0 @ X28)
% 0.20/0.59          | ~ (l1_pre_topc @ X31)
% 0.20/0.59          | ~ (v2_pre_topc @ X31)
% 0.20/0.59          | (v2_struct_0 @ X31))),
% 0.20/0.59      inference('cnf', [status(esa)], [t87_tmap_1])).
% 0.20/0.59  thf('112', plain,
% 0.20/0.59      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X31)
% 0.20/0.59          | ~ (v2_pre_topc @ X31)
% 0.20/0.59          | ~ (l1_pre_topc @ X31)
% 0.20/0.59          | (v2_struct_0 @ X28)
% 0.20/0.59          | ~ (v1_funct_1 @ X32)
% 0.20/0.59          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X31))
% 0.20/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X31))))
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.59          | (r1_tmap_1 @ X27 @ X31 @ X32 @ X30)
% 0.20/0.59          | ~ (r1_tmap_1 @ X28 @ X31 @ 
% 0.20/0.59               (k3_tmap_1 @ X26 @ X31 @ X27 @ X28 @ X32) @ X30)
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.20/0.59          | ~ (m1_pre_topc @ X28 @ X27)
% 0.20/0.59          | ~ (m1_pre_topc @ X28 @ X26)
% 0.20/0.59          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.20/0.59          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.59          | (v2_struct_0 @ X27)
% 0.20/0.59          | ~ (l1_pre_topc @ X26)
% 0.20/0.59          | ~ (v2_pre_topc @ X26)
% 0.20/0.59          | (v2_struct_0 @ X26))),
% 0.20/0.59      inference('simplify', [status(thm)], ['111'])).
% 0.20/0.59  thf('113', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59          | ~ (v1_tsep_1 @ X1 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.59               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.59          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59          | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['110', '112'])).
% 0.20/0.59  thf('114', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('115', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('117', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('118', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59          | ~ (v1_tsep_1 @ X1 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.59               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.20/0.59  thf('119', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.59             (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.59              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.59             X0)
% 0.20/0.59          | (v2_struct_0 @ sk_B)
% 0.20/0.59          | (v2_struct_0 @ sk_C)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.59          | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.59          | (v2_struct_0 @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['109', '118'])).
% 0.20/0.59  thf('120', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.59  thf('121', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.59  thf('122', plain,
% 0.20/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('123', plain,
% 0.20/0.59      (![X6 : $i, X7 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X6)
% 0.20/0.59          | ~ (m1_pre_topc @ X7 @ 
% 0.20/0.59               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.59          | (m1_pre_topc @ X7 @ X6)
% 0.20/0.59          | ~ (l1_pre_topc @ X7))),
% 0.20/0.59      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.59  thf('124', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.59  thf('125', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('126', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (m1_pre_topc @ X0 @ sk_C))),
% 0.20/0.59      inference('demod', [status(thm)], ['124', '125'])).
% 0.20/0.59  thf('127', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['121', '126'])).
% 0.20/0.59  thf('128', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('129', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['127', '128'])).
% 0.20/0.59  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['127', '128'])).
% 0.20/0.59  thf(fc10_tops_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.59  thf('131', plain,
% 0.20/0.59      (![X8 : $i]:
% 0.20/0.59         ((v3_pre_topc @ (k2_struct_0 @ X8) @ X8)
% 0.20/0.59          | ~ (l1_pre_topc @ X8)
% 0.20/0.59          | ~ (v2_pre_topc @ X8))),
% 0.20/0.59      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.20/0.59  thf('132', plain,
% 0.20/0.59      (![X2 : $i]:
% 0.20/0.59         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.59  thf('133', plain,
% 0.20/0.59      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.59  thf(t1_tsep_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.59           ( m1_subset_1 @
% 0.20/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.59  thf('134', plain,
% 0.20/0.59      (![X20 : $i, X21 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.59          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.20/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.59          | ~ (l1_pre_topc @ X21))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.59  thf('135', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['133', '134'])).
% 0.20/0.59  thf('136', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['135'])).
% 0.20/0.59  thf(t16_tsep_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.59                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.59                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('137', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.59          | ((X19) != (u1_struct_0 @ X17))
% 0.20/0.59          | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.59          | (v1_tsep_1 @ X17 @ X18)
% 0.20/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.59          | ~ (l1_pre_topc @ X18)
% 0.20/0.59          | ~ (v2_pre_topc @ X18))),
% 0.20/0.59      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.59  thf('138', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (~ (v2_pre_topc @ X18)
% 0.20/0.59          | ~ (l1_pre_topc @ X18)
% 0.20/0.59          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.20/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.59          | (v1_tsep_1 @ X17 @ X18)
% 0.20/0.59          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.20/0.59          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.20/0.59      inference('simplify', [status(thm)], ['137'])).
% 0.20/0.59  thf('139', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X0)
% 0.20/0.59          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.59          | (v1_tsep_1 @ X0 @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['136', '138'])).
% 0.20/0.59  thf('140', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v1_tsep_1 @ X0 @ X0)
% 0.20/0.59          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['139'])).
% 0.20/0.59  thf('141', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.20/0.59          | ~ (l1_struct_0 @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X0)
% 0.20/0.59          | (v1_tsep_1 @ X0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['132', '140'])).
% 0.20/0.59  thf('142', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v1_tsep_1 @ X0 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_struct_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['131', '141'])).
% 0.20/0.59  thf('143', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (l1_struct_0 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X0)
% 0.20/0.59          | (v1_tsep_1 @ X0 @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['142'])).
% 0.20/0.59  thf('144', plain,
% 0.20/0.59      ((~ (v2_pre_topc @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_C)
% 0.20/0.59        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.20/0.59        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['130', '143'])).
% 0.20/0.59  thf('145', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.59  thf('146', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('147', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.59  thf('148', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.20/0.59  thf('149', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.20/0.59  thf('150', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('151', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.59  thf('152', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.59             (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.59              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.59             X0)
% 0.20/0.59          | (v2_struct_0 @ sk_B)
% 0.20/0.59          | (v2_struct_0 @ sk_C)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | (v2_struct_0 @ sk_C))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['119', '120', '129', '148', '149', '150', '151'])).
% 0.20/0.59  thf('153', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.59          | (v2_struct_0 @ sk_C)
% 0.20/0.59          | (v2_struct_0 @ sk_B)
% 0.20/0.59          | ~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.59               (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 0.20/0.59                sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.59               X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['152'])).
% 0.20/0.59  thf('154', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.59        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.59        | (v2_struct_0 @ sk_D))),
% 0.20/0.59      inference('sup-', [status(thm)], ['79', '153'])).
% 0.20/0.59  thf('155', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('156', plain, (((sk_F) = (sk_G))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('157', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.59      inference('demod', [status(thm)], ['155', '156'])).
% 0.20/0.59  thf('158', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('159', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.59        | (v2_struct_0 @ sk_D))),
% 0.20/0.59      inference('demod', [status(thm)], ['154', '157', '158'])).
% 0.20/0.59  thf('160', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('161', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['159', '160'])).
% 0.20/0.59  thf('162', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('163', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.20/0.59      inference('clc', [status(thm)], ['161', '162'])).
% 0.20/0.59  thf('164', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('165', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('clc', [status(thm)], ['163', '164'])).
% 0.20/0.59  thf('166', plain, ($false), inference('demod', [status(thm)], ['0', '165'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
