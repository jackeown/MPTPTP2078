%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.grhtAB2JmF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:37 EST 2020

% Result     : Theorem 3.63s
% Output     : Refutation 3.63s
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

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

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

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

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
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('81',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_tsep_1 @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ( X28 != X29 )
      | ~ ( r1_tmap_1 @ X27 @ X30 @ ( k3_tmap_1 @ X25 @ X30 @ X26 @ X27 @ X31 ) @ X29 )
      | ( r1_tmap_1 @ X26 @ X30 @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t87_tmap_1])).

thf('112',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X26 @ X30 @ X31 @ X29 )
      | ~ ( r1_tmap_1 @ X27 @ X30 @ ( k3_tmap_1 @ X25 @ X30 @ X26 @ X27 @ X31 ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( v1_tsep_1 @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('134',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.grhtAB2JmF
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.63/3.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.63/3.84  % Solved by: fo/fo7.sh
% 3.63/3.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.63/3.84  % done 5226 iterations in 3.376s
% 3.63/3.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.63/3.84  % SZS output start Refutation
% 3.63/3.84  thf(sk_F_type, type, sk_F: $i).
% 3.63/3.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.63/3.84  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.63/3.84  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 3.63/3.84  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.63/3.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.63/3.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.63/3.84  thf(sk_B_type, type, sk_B: $i).
% 3.63/3.84  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.63/3.84  thf(sk_G_type, type, sk_G: $i).
% 3.63/3.84  thf(sk_C_type, type, sk_C: $i).
% 3.63/3.84  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 3.63/3.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.63/3.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.63/3.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.63/3.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.63/3.84  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.63/3.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.63/3.84  thf(sk_A_type, type, sk_A: $i).
% 3.63/3.84  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.63/3.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.63/3.84  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 3.63/3.84  thf(sk_D_type, type, sk_D: $i).
% 3.63/3.84  thf(sk_E_type, type, sk_E: $i).
% 3.63/3.84  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 3.63/3.84  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.63/3.84  thf(t88_tmap_1, conjecture,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.63/3.84       ( ![B:$i]:
% 3.63/3.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.63/3.84             ( l1_pre_topc @ B ) ) =>
% 3.63/3.84           ( ![C:$i]:
% 3.63/3.84             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.63/3.84               ( ![D:$i]:
% 3.63/3.84                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.63/3.84                   ( ![E:$i]:
% 3.63/3.84                     ( ( ( v1_funct_1 @ E ) & 
% 3.63/3.84                         ( v1_funct_2 @
% 3.63/3.84                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 3.63/3.84                         ( m1_subset_1 @
% 3.63/3.84                           E @ 
% 3.63/3.84                           ( k1_zfmisc_1 @
% 3.63/3.84                             ( k2_zfmisc_1 @
% 3.63/3.84                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.63/3.84                       ( ( ( g1_pre_topc @
% 3.63/3.84                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 3.63/3.84                           ( D ) ) =>
% 3.63/3.84                         ( ![F:$i]:
% 3.63/3.84                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 3.63/3.84                             ( ![G:$i]:
% 3.63/3.84                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 3.63/3.84                                 ( ( ( ( F ) = ( G ) ) & 
% 3.63/3.84                                     ( r1_tmap_1 @
% 3.63/3.84                                       C @ B @ 
% 3.63/3.84                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 3.63/3.84                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.63/3.84  thf(zf_stmt_0, negated_conjecture,
% 3.63/3.84    (~( ![A:$i]:
% 3.63/3.84        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.63/3.84            ( l1_pre_topc @ A ) ) =>
% 3.63/3.84          ( ![B:$i]:
% 3.63/3.84            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.63/3.84                ( l1_pre_topc @ B ) ) =>
% 3.63/3.84              ( ![C:$i]:
% 3.63/3.84                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.63/3.84                  ( ![D:$i]:
% 3.63/3.84                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.63/3.84                      ( ![E:$i]:
% 3.63/3.84                        ( ( ( v1_funct_1 @ E ) & 
% 3.63/3.84                            ( v1_funct_2 @
% 3.63/3.84                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 3.63/3.84                            ( m1_subset_1 @
% 3.63/3.84                              E @ 
% 3.63/3.84                              ( k1_zfmisc_1 @
% 3.63/3.84                                ( k2_zfmisc_1 @
% 3.63/3.84                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.63/3.84                          ( ( ( g1_pre_topc @
% 3.63/3.84                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 3.63/3.84                              ( D ) ) =>
% 3.63/3.84                            ( ![F:$i]:
% 3.63/3.84                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 3.63/3.84                                ( ![G:$i]:
% 3.63/3.84                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 3.63/3.84                                    ( ( ( ( F ) = ( G ) ) & 
% 3.63/3.84                                        ( r1_tmap_1 @
% 3.63/3.84                                          C @ B @ 
% 3.63/3.84                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 3.63/3.84                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.63/3.84    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 3.63/3.84  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('1', plain,
% 3.63/3.84      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 3.63/3.84        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('2', plain, (((sk_F) = (sk_G))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('3', plain,
% 3.63/3.84      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 3.63/3.84        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 3.63/3.84      inference('demod', [status(thm)], ['1', '2'])).
% 3.63/3.84  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('5', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('6', plain,
% 3.63/3.84      ((m1_subset_1 @ sk_E @ 
% 3.63/3.84        (k1_zfmisc_1 @ 
% 3.63/3.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf(d5_tmap_1, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.63/3.84       ( ![B:$i]:
% 3.63/3.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.63/3.84             ( l1_pre_topc @ B ) ) =>
% 3.63/3.84           ( ![C:$i]:
% 3.63/3.84             ( ( m1_pre_topc @ C @ A ) =>
% 3.63/3.84               ( ![D:$i]:
% 3.63/3.84                 ( ( m1_pre_topc @ D @ A ) =>
% 3.63/3.84                   ( ![E:$i]:
% 3.63/3.84                     ( ( ( v1_funct_1 @ E ) & 
% 3.63/3.84                         ( v1_funct_2 @
% 3.63/3.84                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 3.63/3.84                         ( m1_subset_1 @
% 3.63/3.84                           E @ 
% 3.63/3.84                           ( k1_zfmisc_1 @
% 3.63/3.84                             ( k2_zfmisc_1 @
% 3.63/3.84                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.63/3.84                       ( ( m1_pre_topc @ D @ C ) =>
% 3.63/3.84                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 3.63/3.84                           ( k2_partfun1 @
% 3.63/3.84                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 3.63/3.84                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.63/3.84  thf('7', plain,
% 3.63/3.84      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X9)
% 3.63/3.84          | ~ (v2_pre_topc @ X9)
% 3.63/3.84          | ~ (l1_pre_topc @ X9)
% 3.63/3.84          | ~ (m1_pre_topc @ X10 @ X11)
% 3.63/3.84          | ~ (m1_pre_topc @ X10 @ X12)
% 3.63/3.84          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 3.63/3.84                 X13 @ (u1_struct_0 @ X10)))
% 3.63/3.84          | ~ (m1_subset_1 @ X13 @ 
% 3.63/3.84               (k1_zfmisc_1 @ 
% 3.63/3.84                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 3.63/3.84          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 3.63/3.84          | ~ (v1_funct_1 @ X13)
% 3.63/3.84          | ~ (m1_pre_topc @ X12 @ X11)
% 3.63/3.84          | ~ (l1_pre_topc @ X11)
% 3.63/3.84          | ~ (v2_pre_topc @ X11)
% 3.63/3.84          | (v2_struct_0 @ X11))),
% 3.63/3.84      inference('cnf', [status(esa)], [d5_tmap_1])).
% 3.63/3.84  thf('8', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.63/3.84          | ~ (v1_funct_1 @ sk_E)
% 3.63/3.84          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.63/3.84          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X1)))
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ sk_B)
% 3.63/3.84          | ~ (v2_pre_topc @ sk_B)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('sup-', [status(thm)], ['6', '7'])).
% 3.63/3.84  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('10', plain,
% 3.63/3.84      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('13', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.63/3.84          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X1)))
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ X0)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 3.63/3.84  thf('14', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ sk_A)
% 3.63/3.84          | ~ (v2_pre_topc @ sk_A)
% 3.63/3.84          | (v2_struct_0 @ sk_A))),
% 3.63/3.84      inference('sup-', [status(thm)], ['5', '13'])).
% 3.63/3.84  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('17', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | (v2_struct_0 @ sk_A))),
% 3.63/3.84      inference('demod', [status(thm)], ['14', '15', '16'])).
% 3.63/3.84  thf('18', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_A)
% 3.63/3.84        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (u1_struct_0 @ sk_C)))
% 3.63/3.84        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 3.63/3.84        | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('sup-', [status(thm)], ['4', '17'])).
% 3.63/3.84  thf('19', plain,
% 3.63/3.84      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf(t2_tsep_1, axiom,
% 3.63/3.84    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 3.63/3.84  thf('20', plain,
% 3.63/3.84      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 3.63/3.84      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.63/3.84  thf(t65_pre_topc, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( l1_pre_topc @ A ) =>
% 3.63/3.84       ( ![B:$i]:
% 3.63/3.84         ( ( l1_pre_topc @ B ) =>
% 3.63/3.84           ( ( m1_pre_topc @ A @ B ) <=>
% 3.63/3.84             ( m1_pre_topc @
% 3.63/3.84               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 3.63/3.84  thf('21', plain,
% 3.63/3.84      (![X6 : $i, X7 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X6)
% 3.63/3.84          | ~ (m1_pre_topc @ X7 @ X6)
% 3.63/3.84          | (m1_pre_topc @ X7 @ 
% 3.63/3.84             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 3.63/3.84          | ~ (l1_pre_topc @ X7))),
% 3.63/3.84      inference('cnf', [status(esa)], [t65_pre_topc])).
% 3.63/3.84  thf('22', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | (m1_pre_topc @ X0 @ 
% 3.63/3.84             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ X0))),
% 3.63/3.84      inference('sup-', [status(thm)], ['20', '21'])).
% 3.63/3.84  thf('23', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((m1_pre_topc @ X0 @ 
% 3.63/3.84           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ X0))),
% 3.63/3.84      inference('simplify', [status(thm)], ['22'])).
% 3.63/3.84  thf('24', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 3.63/3.84      inference('sup+', [status(thm)], ['19', '23'])).
% 3.63/3.84  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf(dt_m1_pre_topc, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( l1_pre_topc @ A ) =>
% 3.63/3.84       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.63/3.84  thf('26', plain,
% 3.63/3.84      (![X4 : $i, X5 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 3.63/3.84      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.63/3.84  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['25', '26'])).
% 3.63/3.84  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['24', '29'])).
% 3.63/3.84  thf('31', plain,
% 3.63/3.84      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 3.63/3.84      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.63/3.84  thf('32', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.63/3.84          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X1)))
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ X0)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 3.63/3.84  thf('33', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ sk_D)
% 3.63/3.84          | (v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ sk_D)
% 3.63/3.84          | ~ (v2_pre_topc @ sk_D)
% 3.63/3.84          | (v2_struct_0 @ sk_D))),
% 3.63/3.84      inference('sup-', [status(thm)], ['31', '32'])).
% 3.63/3.84  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('35', plain,
% 3.63/3.84      (![X4 : $i, X5 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 3.63/3.84      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.63/3.84  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 3.63/3.84      inference('sup-', [status(thm)], ['34', '35'])).
% 3.63/3.84  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('38', plain, ((l1_pre_topc @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['36', '37'])).
% 3.63/3.84  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['36', '37'])).
% 3.63/3.84  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf(cc1_pre_topc, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.63/3.84       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 3.63/3.84  thf('41', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X0 @ X1)
% 3.63/3.84          | (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X1)
% 3.63/3.84          | ~ (v2_pre_topc @ X1))),
% 3.63/3.84      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 3.63/3.84  thf('42', plain,
% 3.63/3.84      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 3.63/3.84      inference('sup-', [status(thm)], ['40', '41'])).
% 3.63/3.84  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('45', plain, ((v2_pre_topc @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['42', '43', '44'])).
% 3.63/3.84  thf('46', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | (v2_struct_0 @ sk_D))),
% 3.63/3.84      inference('demod', [status(thm)], ['33', '38', '39', '45'])).
% 3.63/3.84  thf('47', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('simplify', [status(thm)], ['46'])).
% 3.63/3.84  thf('48', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_B)
% 3.63/3.84        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (u1_struct_0 @ sk_C)))
% 3.63/3.84        | (v2_struct_0 @ sk_D))),
% 3.63/3.84      inference('sup-', [status(thm)], ['30', '47'])).
% 3.63/3.84  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('50', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_D)
% 3.63/3.84        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (u1_struct_0 @ sk_C))))),
% 3.63/3.84      inference('clc', [status(thm)], ['48', '49'])).
% 3.63/3.84  thf('51', plain, (~ (v2_struct_0 @ sk_D)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('52', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (u1_struct_0 @ sk_C)))),
% 3.63/3.84      inference('clc', [status(thm)], ['50', '51'])).
% 3.63/3.84  thf(d3_struct_0, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.63/3.84  thf('53', plain,
% 3.63/3.84      (![X2 : $i]:
% 3.63/3.84         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 3.63/3.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.63/3.84  thf('54', plain,
% 3.63/3.84      (![X2 : $i]:
% 3.63/3.84         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 3.63/3.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.63/3.84  thf('55', plain,
% 3.63/3.84      (![X2 : $i]:
% 3.63/3.84         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 3.63/3.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.63/3.84  thf('56', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (u1_struct_0 @ sk_C)))),
% 3.63/3.84      inference('clc', [status(thm)], ['50', '51'])).
% 3.63/3.84  thf('57', plain,
% 3.63/3.84      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84          = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84             sk_E @ (u1_struct_0 @ sk_C)))
% 3.63/3.84        | ~ (l1_struct_0 @ sk_D))),
% 3.63/3.84      inference('sup+', [status(thm)], ['55', '56'])).
% 3.63/3.84  thf('58', plain, ((l1_pre_topc @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['36', '37'])).
% 3.63/3.84  thf(dt_l1_pre_topc, axiom,
% 3.63/3.84    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.63/3.84  thf('59', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 3.63/3.84      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.63/3.84  thf('60', plain, ((l1_struct_0 @ sk_D)),
% 3.63/3.84      inference('sup-', [status(thm)], ['58', '59'])).
% 3.63/3.84  thf('61', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (u1_struct_0 @ sk_C)))),
% 3.63/3.84      inference('demod', [status(thm)], ['57', '60'])).
% 3.63/3.84  thf('62', plain,
% 3.63/3.84      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84          = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84             sk_E @ (u1_struct_0 @ sk_C)))
% 3.63/3.84        | ~ (l1_struct_0 @ sk_B))),
% 3.63/3.84      inference('sup+', [status(thm)], ['54', '61'])).
% 3.63/3.84  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('64', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 3.63/3.84      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.63/3.84  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 3.63/3.84      inference('sup-', [status(thm)], ['63', '64'])).
% 3.63/3.84  thf('66', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (u1_struct_0 @ sk_C)))),
% 3.63/3.84      inference('demod', [status(thm)], ['62', '65'])).
% 3.63/3.84  thf('67', plain,
% 3.63/3.84      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84          = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84             sk_E @ (k2_struct_0 @ sk_C)))
% 3.63/3.84        | ~ (l1_struct_0 @ sk_C))),
% 3.63/3.84      inference('sup+', [status(thm)], ['53', '66'])).
% 3.63/3.84  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('69', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 3.63/3.84      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.63/3.84  thf('70', plain, ((l1_struct_0 @ sk_C)),
% 3.63/3.84      inference('sup-', [status(thm)], ['68', '69'])).
% 3.63/3.84  thf('71', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (k2_struct_0 @ sk_C)))),
% 3.63/3.84      inference('demod', [status(thm)], ['67', '70'])).
% 3.63/3.84  thf('72', plain,
% 3.63/3.84      (((k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84         (k2_struct_0 @ sk_C))
% 3.63/3.84         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (u1_struct_0 @ sk_C)))),
% 3.63/3.84      inference('demod', [status(thm)], ['52', '71'])).
% 3.63/3.84  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['24', '29'])).
% 3.63/3.84  thf('74', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_A)
% 3.63/3.84        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (k2_struct_0 @ sk_C)))
% 3.63/3.84        | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('demod', [status(thm)], ['18', '72', '73'])).
% 3.63/3.84  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('76', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_B)
% 3.63/3.84        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (k2_struct_0 @ sk_C))))),
% 3.63/3.84      inference('clc', [status(thm)], ['74', '75'])).
% 3.63/3.84  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('78', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (k2_struct_0 @ sk_C)))),
% 3.63/3.84      inference('clc', [status(thm)], ['76', '77'])).
% 3.63/3.84  thf('79', plain,
% 3.63/3.84      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 3.63/3.84        (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84         (k2_struct_0 @ sk_C)) @ 
% 3.63/3.84        sk_F)),
% 3.63/3.84      inference('demod', [status(thm)], ['3', '78'])).
% 3.63/3.84  thf('80', plain,
% 3.63/3.84      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 3.63/3.84      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.63/3.84  thf('81', plain,
% 3.63/3.84      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('82', plain,
% 3.63/3.84      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 3.63/3.84      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.63/3.84  thf('83', plain,
% 3.63/3.84      (![X6 : $i, X7 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X6)
% 3.63/3.84          | ~ (m1_pre_topc @ X7 @ 
% 3.63/3.84               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 3.63/3.84          | (m1_pre_topc @ X7 @ X6)
% 3.63/3.84          | ~ (l1_pre_topc @ X7))),
% 3.63/3.84      inference('cnf', [status(esa)], [t65_pre_topc])).
% 3.63/3.84  thf('84', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ 
% 3.63/3.84             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ 
% 3.63/3.84               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.63/3.84          | (m1_pre_topc @ 
% 3.63/3.84             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0))),
% 3.63/3.84      inference('sup-', [status(thm)], ['82', '83'])).
% 3.63/3.84  thf('85', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X0)
% 3.63/3.84          | (m1_pre_topc @ 
% 3.63/3.84             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ 
% 3.63/3.84               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.63/3.84      inference('simplify', [status(thm)], ['84'])).
% 3.63/3.84  thf('86', plain,
% 3.63/3.84      ((~ (l1_pre_topc @ sk_D)
% 3.63/3.84        | (m1_pre_topc @ 
% 3.63/3.84           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 3.63/3.84        | ~ (l1_pre_topc @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['81', '85'])).
% 3.63/3.84  thf('87', plain, ((l1_pre_topc @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['36', '37'])).
% 3.63/3.84  thf('88', plain,
% 3.63/3.84      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('89', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 3.63/3.84  thf('91', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.63/3.84          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X1)))
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ X0)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 3.63/3.84  thf('92', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ sk_C)
% 3.63/3.84          | ~ (v2_pre_topc @ sk_C)
% 3.63/3.84          | (v2_struct_0 @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['90', '91'])).
% 3.63/3.84  thf('93', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('94', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('95', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X0 @ X1)
% 3.63/3.84          | (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X1)
% 3.63/3.84          | ~ (v2_pre_topc @ X1))),
% 3.63/3.84      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 3.63/3.84  thf('96', plain,
% 3.63/3.84      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['94', '95'])).
% 3.63/3.84  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('99', plain, ((v2_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.63/3.84  thf('100', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_C)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ sk_E)
% 3.63/3.84              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84                 sk_E @ (u1_struct_0 @ X0)))
% 3.63/3.84          | (v2_struct_0 @ sk_C))),
% 3.63/3.84      inference('demod', [status(thm)], ['92', '93', '99'])).
% 3.63/3.84  thf('101', plain,
% 3.63/3.84      ((~ (l1_pre_topc @ sk_C)
% 3.63/3.84        | (v2_struct_0 @ sk_C)
% 3.63/3.84        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (u1_struct_0 @ sk_C)))
% 3.63/3.84        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 3.63/3.84        | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('sup-', [status(thm)], ['80', '100'])).
% 3.63/3.84  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('103', plain,
% 3.63/3.84      (((k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84         (k2_struct_0 @ sk_C))
% 3.63/3.84         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (u1_struct_0 @ sk_C)))),
% 3.63/3.84      inference('demod', [status(thm)], ['52', '71'])).
% 3.63/3.84  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['24', '29'])).
% 3.63/3.84  thf('105', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_C)
% 3.63/3.84        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (k2_struct_0 @ sk_C)))
% 3.63/3.84        | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 3.63/3.84  thf('106', plain, (~ (v2_struct_0 @ sk_C)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('107', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_B)
% 3.63/3.84        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84            = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84               sk_E @ (k2_struct_0 @ sk_C))))),
% 3.63/3.84      inference('clc', [status(thm)], ['105', '106'])).
% 3.63/3.84  thf('108', plain, (~ (v2_struct_0 @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('109', plain,
% 3.63/3.84      (((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_C @ sk_E)
% 3.63/3.84         = (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 3.63/3.84            (k2_struct_0 @ sk_C)))),
% 3.63/3.84      inference('clc', [status(thm)], ['107', '108'])).
% 3.63/3.84  thf('110', plain,
% 3.63/3.84      ((m1_subset_1 @ sk_E @ 
% 3.63/3.84        (k1_zfmisc_1 @ 
% 3.63/3.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf(t87_tmap_1, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.63/3.84       ( ![B:$i]:
% 3.63/3.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.63/3.84             ( l1_pre_topc @ B ) ) =>
% 3.63/3.84           ( ![C:$i]:
% 3.63/3.84             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 3.63/3.84               ( ![D:$i]:
% 3.63/3.84                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 3.63/3.84                   ( ![E:$i]:
% 3.63/3.84                     ( ( ( v1_funct_1 @ E ) & 
% 3.63/3.84                         ( v1_funct_2 @
% 3.63/3.84                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 3.63/3.84                         ( m1_subset_1 @
% 3.63/3.84                           E @ 
% 3.63/3.84                           ( k1_zfmisc_1 @
% 3.63/3.84                             ( k2_zfmisc_1 @
% 3.63/3.84                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 3.63/3.84                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 3.63/3.84                           ( m1_pre_topc @ C @ D ) ) =>
% 3.63/3.84                         ( ![F:$i]:
% 3.63/3.84                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 3.63/3.84                             ( ![G:$i]:
% 3.63/3.84                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 3.63/3.84                                 ( ( ( F ) = ( G ) ) =>
% 3.63/3.84                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 3.63/3.84                                     ( r1_tmap_1 @
% 3.63/3.84                                       C @ A @ 
% 3.63/3.84                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.63/3.84  thf('111', plain,
% 3.63/3.84      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X25)
% 3.63/3.84          | ~ (v2_pre_topc @ X25)
% 3.63/3.84          | ~ (l1_pre_topc @ X25)
% 3.63/3.84          | (v2_struct_0 @ X26)
% 3.63/3.84          | ~ (m1_pre_topc @ X26 @ X25)
% 3.63/3.84          | ~ (v1_tsep_1 @ X27 @ X25)
% 3.63/3.84          | ~ (m1_pre_topc @ X27 @ X25)
% 3.63/3.84          | ~ (m1_pre_topc @ X27 @ X26)
% 3.63/3.84          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 3.63/3.84          | ((X28) != (X29))
% 3.63/3.84          | ~ (r1_tmap_1 @ X27 @ X30 @ 
% 3.63/3.84               (k3_tmap_1 @ X25 @ X30 @ X26 @ X27 @ X31) @ X29)
% 3.63/3.84          | (r1_tmap_1 @ X26 @ X30 @ X31 @ X28)
% 3.63/3.84          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 3.63/3.84          | ~ (m1_subset_1 @ X31 @ 
% 3.63/3.84               (k1_zfmisc_1 @ 
% 3.63/3.84                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X30))))
% 3.63/3.84          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X30))
% 3.63/3.84          | ~ (v1_funct_1 @ X31)
% 3.63/3.84          | ~ (m1_pre_topc @ X27 @ X25)
% 3.63/3.84          | (v2_struct_0 @ X27)
% 3.63/3.84          | ~ (l1_pre_topc @ X30)
% 3.63/3.84          | ~ (v2_pre_topc @ X30)
% 3.63/3.84          | (v2_struct_0 @ X30))),
% 3.63/3.84      inference('cnf', [status(esa)], [t87_tmap_1])).
% 3.63/3.84  thf('112', plain,
% 3.63/3.84      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X30)
% 3.63/3.84          | ~ (v2_pre_topc @ X30)
% 3.63/3.84          | ~ (l1_pre_topc @ X30)
% 3.63/3.84          | (v2_struct_0 @ X27)
% 3.63/3.84          | ~ (v1_funct_1 @ X31)
% 3.63/3.84          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X30))
% 3.63/3.84          | ~ (m1_subset_1 @ X31 @ 
% 3.63/3.84               (k1_zfmisc_1 @ 
% 3.63/3.84                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X30))))
% 3.63/3.84          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 3.63/3.84          | (r1_tmap_1 @ X26 @ X30 @ X31 @ X29)
% 3.63/3.84          | ~ (r1_tmap_1 @ X27 @ X30 @ 
% 3.63/3.84               (k3_tmap_1 @ X25 @ X30 @ X26 @ X27 @ X31) @ X29)
% 3.63/3.84          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 3.63/3.84          | ~ (m1_pre_topc @ X27 @ X26)
% 3.63/3.84          | ~ (m1_pre_topc @ X27 @ X25)
% 3.63/3.84          | ~ (v1_tsep_1 @ X27 @ X25)
% 3.63/3.84          | ~ (m1_pre_topc @ X26 @ X25)
% 3.63/3.84          | (v2_struct_0 @ X26)
% 3.63/3.84          | ~ (l1_pre_topc @ X25)
% 3.63/3.84          | ~ (v2_pre_topc @ X25)
% 3.63/3.84          | (v2_struct_0 @ X25))),
% 3.63/3.84      inference('simplify', [status(thm)], ['111'])).
% 3.63/3.84  thf('113', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | (v2_struct_0 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.63/3.84          | ~ (v1_tsep_1 @ X1 @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.63/3.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 3.63/3.84          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 3.63/3.84               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 3.63/3.84          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 3.63/3.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 3.63/3.84          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.63/3.84          | ~ (v1_funct_1 @ sk_E)
% 3.63/3.84          | (v2_struct_0 @ X1)
% 3.63/3.84          | ~ (l1_pre_topc @ sk_B)
% 3.63/3.84          | ~ (v2_pre_topc @ sk_B)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('sup-', [status(thm)], ['110', '112'])).
% 3.63/3.84  thf('114', plain,
% 3.63/3.84      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('115', plain, ((v1_funct_1 @ sk_E)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('117', plain, ((v2_pre_topc @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('118', plain,
% 3.63/3.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.63/3.84         ((v2_struct_0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | (v2_struct_0 @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.63/3.84          | ~ (v1_tsep_1 @ X1 @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.63/3.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 3.63/3.84          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 3.63/3.84               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 3.63/3.84          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 3.63/3.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 3.63/3.84          | (v2_struct_0 @ X1)
% 3.63/3.84          | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 3.63/3.84  thf('119', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 3.63/3.84             (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 3.63/3.84             X0)
% 3.63/3.84          | (v2_struct_0 @ sk_B)
% 3.63/3.84          | (v2_struct_0 @ sk_C)
% 3.63/3.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.63/3.84          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 3.63/3.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 3.63/3.84          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 3.63/3.84          | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 3.63/3.84          | ~ (m1_pre_topc @ sk_D @ sk_C)
% 3.63/3.84          | (v2_struct_0 @ sk_D)
% 3.63/3.84          | ~ (l1_pre_topc @ sk_C)
% 3.63/3.84          | ~ (v2_pre_topc @ sk_C)
% 3.63/3.84          | (v2_struct_0 @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['109', '118'])).
% 3.63/3.84  thf('120', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['24', '29'])).
% 3.63/3.84  thf('121', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 3.63/3.84      inference('demod', [status(thm)], ['24', '29'])).
% 3.63/3.84  thf('122', plain,
% 3.63/3.84      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('123', plain,
% 3.63/3.84      (![X6 : $i, X7 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X6)
% 3.63/3.84          | ~ (m1_pre_topc @ X7 @ 
% 3.63/3.84               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 3.63/3.84          | (m1_pre_topc @ X7 @ X6)
% 3.63/3.84          | ~ (l1_pre_topc @ X7))),
% 3.63/3.84      inference('cnf', [status(esa)], [t65_pre_topc])).
% 3.63/3.84  thf('124', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | (m1_pre_topc @ X0 @ sk_C)
% 3.63/3.84          | ~ (l1_pre_topc @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['122', '123'])).
% 3.63/3.84  thf('125', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('126', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X0 @ sk_D)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | (m1_pre_topc @ X0 @ sk_C))),
% 3.63/3.84      inference('demod', [status(thm)], ['124', '125'])).
% 3.63/3.84  thf('127', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['121', '126'])).
% 3.63/3.84  thf('128', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('129', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['127', '128'])).
% 3.63/3.84  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['127', '128'])).
% 3.63/3.84  thf(fc10_tops_1, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.63/3.84       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 3.63/3.84  thf('131', plain,
% 3.63/3.84      (![X8 : $i]:
% 3.63/3.84         ((v3_pre_topc @ (k2_struct_0 @ X8) @ X8)
% 3.63/3.84          | ~ (l1_pre_topc @ X8)
% 3.63/3.84          | ~ (v2_pre_topc @ X8))),
% 3.63/3.84      inference('cnf', [status(esa)], [fc10_tops_1])).
% 3.63/3.84  thf('132', plain,
% 3.63/3.84      (![X2 : $i]:
% 3.63/3.84         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 3.63/3.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.63/3.84  thf('133', plain,
% 3.63/3.84      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 3.63/3.84      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.63/3.84  thf(t1_tsep_1, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( l1_pre_topc @ A ) =>
% 3.63/3.84       ( ![B:$i]:
% 3.63/3.84         ( ( m1_pre_topc @ B @ A ) =>
% 3.63/3.84           ( m1_subset_1 @
% 3.63/3.84             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.63/3.84  thf('134', plain,
% 3.63/3.84      (![X19 : $i, X20 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X19 @ X20)
% 3.63/3.84          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 3.63/3.84             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.63/3.84          | ~ (l1_pre_topc @ X20))),
% 3.63/3.84      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.63/3.84  thf('135', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.63/3.84             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 3.63/3.84      inference('sup-', [status(thm)], ['133', '134'])).
% 3.63/3.84  thf('136', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.63/3.84           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.63/3.84          | ~ (l1_pre_topc @ X0))),
% 3.63/3.84      inference('simplify', [status(thm)], ['135'])).
% 3.63/3.84  thf(t16_tsep_1, axiom,
% 3.63/3.84    (![A:$i]:
% 3.63/3.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.63/3.84       ( ![B:$i]:
% 3.63/3.84         ( ( m1_pre_topc @ B @ A ) =>
% 3.63/3.84           ( ![C:$i]:
% 3.63/3.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.63/3.84               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 3.63/3.84                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 3.63/3.84                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 3.63/3.84  thf('137', plain,
% 3.63/3.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.63/3.84         (~ (m1_pre_topc @ X16 @ X17)
% 3.63/3.84          | ((X18) != (u1_struct_0 @ X16))
% 3.63/3.84          | ~ (v3_pre_topc @ X18 @ X17)
% 3.63/3.84          | (v1_tsep_1 @ X16 @ X17)
% 3.63/3.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.63/3.84          | ~ (l1_pre_topc @ X17)
% 3.63/3.84          | ~ (v2_pre_topc @ X17))),
% 3.63/3.84      inference('cnf', [status(esa)], [t16_tsep_1])).
% 3.63/3.84  thf('138', plain,
% 3.63/3.84      (![X16 : $i, X17 : $i]:
% 3.63/3.84         (~ (v2_pre_topc @ X17)
% 3.63/3.84          | ~ (l1_pre_topc @ X17)
% 3.63/3.84          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 3.63/3.84               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.63/3.84          | (v1_tsep_1 @ X16 @ X17)
% 3.63/3.84          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 3.63/3.84          | ~ (m1_pre_topc @ X16 @ X17))),
% 3.63/3.84      inference('simplify', [status(thm)], ['137'])).
% 3.63/3.84  thf('139', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ X0)
% 3.63/3.84          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 3.63/3.84          | (v1_tsep_1 @ X0 @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0))),
% 3.63/3.84      inference('sup-', [status(thm)], ['136', '138'])).
% 3.63/3.84  thf('140', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (v2_pre_topc @ X0)
% 3.63/3.84          | (v1_tsep_1 @ X0 @ X0)
% 3.63/3.84          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0))),
% 3.63/3.84      inference('simplify', [status(thm)], ['139'])).
% 3.63/3.84  thf('141', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 3.63/3.84          | ~ (l1_struct_0 @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ X0)
% 3.63/3.84          | (v1_tsep_1 @ X0 @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0))),
% 3.63/3.84      inference('sup-', [status(thm)], ['132', '140'])).
% 3.63/3.84  thf('142', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (v2_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0)
% 3.63/3.84          | (v1_tsep_1 @ X0 @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (l1_struct_0 @ X0))),
% 3.63/3.84      inference('sup-', [status(thm)], ['131', '141'])).
% 3.63/3.84  thf('143', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (l1_struct_0 @ X0)
% 3.63/3.84          | ~ (m1_pre_topc @ X0 @ X0)
% 3.63/3.84          | (v1_tsep_1 @ X0 @ X0)
% 3.63/3.84          | ~ (l1_pre_topc @ X0)
% 3.63/3.84          | ~ (v2_pre_topc @ X0))),
% 3.63/3.84      inference('simplify', [status(thm)], ['142'])).
% 3.63/3.84  thf('144', plain,
% 3.63/3.84      ((~ (v2_pre_topc @ sk_C)
% 3.63/3.84        | ~ (l1_pre_topc @ sk_C)
% 3.63/3.84        | (v1_tsep_1 @ sk_C @ sk_C)
% 3.63/3.84        | ~ (l1_struct_0 @ sk_C))),
% 3.63/3.84      inference('sup-', [status(thm)], ['130', '143'])).
% 3.63/3.84  thf('145', plain, ((v2_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.63/3.84  thf('146', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('147', plain, ((l1_struct_0 @ sk_C)),
% 3.63/3.84      inference('sup-', [status(thm)], ['68', '69'])).
% 3.63/3.84  thf('148', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 3.63/3.84  thf('149', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 3.63/3.84  thf('150', plain, ((l1_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['27', '28'])).
% 3.63/3.84  thf('151', plain, ((v2_pre_topc @ sk_C)),
% 3.63/3.84      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.63/3.84  thf('152', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 3.63/3.84             (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 3.63/3.84             X0)
% 3.63/3.84          | (v2_struct_0 @ sk_B)
% 3.63/3.84          | (v2_struct_0 @ sk_C)
% 3.63/3.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.63/3.84          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 3.63/3.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 3.63/3.84          | (v2_struct_0 @ sk_D)
% 3.63/3.84          | (v2_struct_0 @ sk_C))),
% 3.63/3.84      inference('demod', [status(thm)],
% 3.63/3.84                ['119', '120', '129', '148', '149', '150', '151'])).
% 3.63/3.84  thf('153', plain,
% 3.63/3.84      (![X0 : $i]:
% 3.63/3.84         ((v2_struct_0 @ sk_D)
% 3.63/3.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 3.63/3.84          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 3.63/3.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.63/3.84          | (v2_struct_0 @ sk_C)
% 3.63/3.84          | (v2_struct_0 @ sk_B)
% 3.63/3.84          | ~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 3.63/3.84               (k2_partfun1 @ (k2_struct_0 @ sk_D) @ (k2_struct_0 @ sk_B) @ 
% 3.63/3.84                sk_E @ (k2_struct_0 @ sk_C)) @ 
% 3.63/3.84               X0))),
% 3.63/3.84      inference('simplify', [status(thm)], ['152'])).
% 3.63/3.84  thf('154', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_B)
% 3.63/3.84        | (v2_struct_0 @ sk_C)
% 3.63/3.84        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 3.63/3.84        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 3.63/3.84        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 3.63/3.84        | (v2_struct_0 @ sk_D))),
% 3.63/3.84      inference('sup-', [status(thm)], ['79', '153'])).
% 3.63/3.84  thf('155', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('156', plain, (((sk_F) = (sk_G))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('157', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 3.63/3.84      inference('demod', [status(thm)], ['155', '156'])).
% 3.63/3.84  thf('158', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('159', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_B)
% 3.63/3.84        | (v2_struct_0 @ sk_C)
% 3.63/3.84        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 3.63/3.84        | (v2_struct_0 @ sk_D))),
% 3.63/3.84      inference('demod', [status(thm)], ['154', '157', '158'])).
% 3.63/3.84  thf('160', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('161', plain,
% 3.63/3.84      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 3.63/3.84      inference('sup-', [status(thm)], ['159', '160'])).
% 3.63/3.84  thf('162', plain, (~ (v2_struct_0 @ sk_D)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('163', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 3.63/3.84      inference('clc', [status(thm)], ['161', '162'])).
% 3.63/3.84  thf('164', plain, (~ (v2_struct_0 @ sk_B)),
% 3.63/3.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.63/3.84  thf('165', plain, ((v2_struct_0 @ sk_C)),
% 3.63/3.84      inference('clc', [status(thm)], ['163', '164'])).
% 3.63/3.84  thf('166', plain, ($false), inference('demod', [status(thm)], ['0', '165'])).
% 3.63/3.84  
% 3.63/3.84  % SZS output end Refutation
% 3.63/3.84  
% 3.63/3.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
