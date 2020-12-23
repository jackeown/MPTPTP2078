%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jnKrbfQg6N

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:28 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  186 (1778 expanded)
%              Number of leaves         :   41 ( 542 expanded)
%              Depth                    :   21
%              Number of atoms          : 1603 (47531 expanded)
%              Number of equality atoms :   58 (1549 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( g1_pre_topc @ X11 @ X12 )
       != ( g1_pre_topc @ X9 @ X10 ) )
      | ( X11 = X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('15',plain,
    ( ( v1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('18',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','21','26'])).

thf('28',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','27','28','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','35'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','27','28','33','34'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('42',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('53',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','21','26'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['47','50'])).

thf('56',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('57',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['47','50'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['44','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['40','41'])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

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

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ( X29 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
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
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('70',plain,(
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
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','27','28','33','34'])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('77',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
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
    inference(demod,[status(thm)],['71','72','77','78','79'])).

thf('81',plain,
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
    inference('sup-',[status(thm)],['3','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('84',plain,(
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

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

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

thf('92',plain,(
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

thf('93',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('96',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('98',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['94','95','101'])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['90','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('105',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('106',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('107',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('108',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('110',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('111',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['112','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('119',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['103','104','105','111','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['117','118'])).

thf('122',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('128',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('130',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('131',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','120','121','128','129','130','131','132','133'])).

thf('135',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['0','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jnKrbfQg6N
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.96/2.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.96/2.18  % Solved by: fo/fo7.sh
% 1.96/2.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.18  % done 2798 iterations in 1.722s
% 1.96/2.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.96/2.18  % SZS output start Refutation
% 1.96/2.18  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.96/2.18  thf(sk_F_type, type, sk_F: $i).
% 1.96/2.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.96/2.18  thf(sk_E_type, type, sk_E: $i).
% 1.96/2.18  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.96/2.18  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.96/2.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.96/2.18  thf(sk_B_type, type, sk_B: $i).
% 1.96/2.18  thf(sk_D_type, type, sk_D: $i).
% 1.96/2.18  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.96/2.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.96/2.18  thf(sk_C_type, type, sk_C: $i).
% 1.96/2.18  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.96/2.18  thf(sk_A_type, type, sk_A: $i).
% 1.96/2.18  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.96/2.18  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.96/2.18  thf(sk_G_type, type, sk_G: $i).
% 1.96/2.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.96/2.18  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.96/2.18  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.96/2.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.96/2.18  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.96/2.18  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.96/2.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.96/2.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.96/2.18  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.96/2.18  thf(t88_tmap_1, conjecture,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.96/2.18       ( ![B:$i]:
% 1.96/2.18         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.96/2.18             ( l1_pre_topc @ B ) ) =>
% 1.96/2.18           ( ![C:$i]:
% 1.96/2.18             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.96/2.18               ( ![D:$i]:
% 1.96/2.18                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.96/2.18                   ( ![E:$i]:
% 1.96/2.18                     ( ( ( v1_funct_1 @ E ) & 
% 1.96/2.18                         ( v1_funct_2 @
% 1.96/2.18                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.96/2.18                         ( m1_subset_1 @
% 1.96/2.18                           E @ 
% 1.96/2.18                           ( k1_zfmisc_1 @
% 1.96/2.18                             ( k2_zfmisc_1 @
% 1.96/2.18                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.96/2.18                       ( ( ( g1_pre_topc @
% 1.96/2.18                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.96/2.18                           ( D ) ) =>
% 1.96/2.18                         ( ![F:$i]:
% 1.96/2.18                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.96/2.18                             ( ![G:$i]:
% 1.96/2.18                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.96/2.18                                 ( ( ( ( F ) = ( G ) ) & 
% 1.96/2.18                                     ( r1_tmap_1 @
% 1.96/2.18                                       C @ B @ 
% 1.96/2.18                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.96/2.18                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.96/2.18  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.18    (~( ![A:$i]:
% 1.96/2.18        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.96/2.18            ( l1_pre_topc @ A ) ) =>
% 1.96/2.18          ( ![B:$i]:
% 1.96/2.18            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.96/2.18                ( l1_pre_topc @ B ) ) =>
% 1.96/2.18              ( ![C:$i]:
% 1.96/2.18                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.96/2.18                  ( ![D:$i]:
% 1.96/2.18                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.96/2.18                      ( ![E:$i]:
% 1.96/2.18                        ( ( ( v1_funct_1 @ E ) & 
% 1.96/2.18                            ( v1_funct_2 @
% 1.96/2.18                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.96/2.18                            ( m1_subset_1 @
% 1.96/2.18                              E @ 
% 1.96/2.18                              ( k1_zfmisc_1 @
% 1.96/2.18                                ( k2_zfmisc_1 @
% 1.96/2.18                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.96/2.18                          ( ( ( g1_pre_topc @
% 1.96/2.18                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.96/2.18                              ( D ) ) =>
% 1.96/2.18                            ( ![F:$i]:
% 1.96/2.18                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.96/2.18                                ( ![G:$i]:
% 1.96/2.18                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.96/2.18                                    ( ( ( ( F ) = ( G ) ) & 
% 1.96/2.18                                        ( r1_tmap_1 @
% 1.96/2.18                                          C @ B @ 
% 1.96/2.18                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.96/2.18                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.96/2.18    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.96/2.18  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('1', plain,
% 1.96/2.18      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.96/2.18        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('2', plain, (((sk_F) = (sk_G))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('3', plain,
% 1.96/2.18      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.96/2.18        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.96/2.18      inference('demod', [status(thm)], ['1', '2'])).
% 1.96/2.18  thf('4', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_E @ 
% 1.96/2.18        (k1_zfmisc_1 @ 
% 1.96/2.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('5', plain,
% 1.96/2.18      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(abstractness_v1_pre_topc, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( l1_pre_topc @ A ) =>
% 1.96/2.18       ( ( v1_pre_topc @ A ) =>
% 1.96/2.18         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.96/2.18  thf('6', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (v1_pre_topc @ X0)
% 1.96/2.18          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.96/2.18          | ~ (l1_pre_topc @ X0))),
% 1.96/2.18      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.96/2.18  thf(dt_u1_pre_topc, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( l1_pre_topc @ A ) =>
% 1.96/2.18       ( m1_subset_1 @
% 1.96/2.18         ( u1_pre_topc @ A ) @ 
% 1.96/2.18         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.96/2.18  thf('7', plain,
% 1.96/2.18      (![X7 : $i]:
% 1.96/2.18         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 1.96/2.18           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 1.96/2.18          | ~ (l1_pre_topc @ X7))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.96/2.18  thf(free_g1_pre_topc, axiom,
% 1.96/2.18    (![A:$i,B:$i]:
% 1.96/2.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.96/2.18       ( ![C:$i,D:$i]:
% 1.96/2.18         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.96/2.18           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.96/2.18  thf('8', plain,
% 1.96/2.18      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.96/2.18         (((g1_pre_topc @ X11 @ X12) != (g1_pre_topc @ X9 @ X10))
% 1.96/2.18          | ((X11) = (X9))
% 1.96/2.18          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 1.96/2.18      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.96/2.18  thf('9', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         (~ (l1_pre_topc @ X0)
% 1.96/2.18          | ((u1_struct_0 @ X0) = (X1))
% 1.96/2.18          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.96/2.18              != (g1_pre_topc @ X1 @ X2)))),
% 1.96/2.18      inference('sup-', [status(thm)], ['7', '8'])).
% 1.96/2.18  thf('10', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | ~ (v1_pre_topc @ X0)
% 1.96/2.18          | ((u1_struct_0 @ X0) = (X2))
% 1.96/2.18          | ~ (l1_pre_topc @ X0))),
% 1.96/2.18      inference('sup-', [status(thm)], ['6', '9'])).
% 1.96/2.18  thf('11', plain,
% 1.96/2.18      (![X1 : $i, X2 : $i]:
% 1.96/2.18         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.96/2.18          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.96/2.18          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.96/2.18      inference('simplify', [status(thm)], ['10'])).
% 1.96/2.18  thf('12', plain,
% 1.96/2.18      ((~ (v1_pre_topc @ sk_D)
% 1.96/2.18        | ~ (l1_pre_topc @ 
% 1.96/2.18             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.96/2.18        | ((u1_struct_0 @ 
% 1.96/2.18            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.96/2.18            = (u1_struct_0 @ sk_C)))),
% 1.96/2.18      inference('sup-', [status(thm)], ['5', '11'])).
% 1.96/2.18  thf('13', plain,
% 1.96/2.18      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(fc6_pre_topc, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.96/2.18       ( ( v1_pre_topc @
% 1.96/2.18           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.96/2.18         ( v2_pre_topc @
% 1.96/2.18           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.96/2.18  thf('14', plain,
% 1.96/2.18      (![X8 : $i]:
% 1.96/2.18         ((v1_pre_topc @ 
% 1.96/2.18           (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 1.96/2.18          | ~ (l1_pre_topc @ X8)
% 1.96/2.18          | ~ (v2_pre_topc @ X8))),
% 1.96/2.18      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 1.96/2.18  thf('15', plain,
% 1.96/2.18      (((v1_pre_topc @ sk_D) | ~ (v2_pre_topc @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.96/2.18      inference('sup+', [status(thm)], ['13', '14'])).
% 1.96/2.18  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(cc1_pre_topc, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.96/2.18       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.96/2.18  thf('17', plain,
% 1.96/2.18      (![X1 : $i, X2 : $i]:
% 1.96/2.18         (~ (m1_pre_topc @ X1 @ X2)
% 1.96/2.18          | (v2_pre_topc @ X1)
% 1.96/2.18          | ~ (l1_pre_topc @ X2)
% 1.96/2.18          | ~ (v2_pre_topc @ X2))),
% 1.96/2.18      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.96/2.18  thf('18', plain,
% 1.96/2.18      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.96/2.18      inference('sup-', [status(thm)], ['16', '17'])).
% 1.96/2.18  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('21', plain, ((v2_pre_topc @ sk_C)),
% 1.96/2.18      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.96/2.18  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf(dt_m1_pre_topc, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( l1_pre_topc @ A ) =>
% 1.96/2.18       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.96/2.18  thf('23', plain,
% 1.96/2.18      (![X5 : $i, X6 : $i]:
% 1.96/2.18         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.96/2.18  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.96/2.18      inference('sup-', [status(thm)], ['22', '23'])).
% 1.96/2.18  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('26', plain, ((l1_pre_topc @ sk_C)),
% 1.96/2.18      inference('demod', [status(thm)], ['24', '25'])).
% 1.96/2.18  thf('27', plain, ((v1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['15', '21', '26'])).
% 1.96/2.18  thf('28', plain,
% 1.96/2.18      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('30', plain,
% 1.96/2.18      (![X5 : $i, X6 : $i]:
% 1.96/2.18         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.96/2.18  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['29', '30'])).
% 1.96/2.18  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['31', '32'])).
% 1.96/2.18  thf('34', plain,
% 1.96/2.18      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('35', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['12', '27', '28', '33', '34'])).
% 1.96/2.18  thf('36', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_E @ 
% 1.96/2.18        (k1_zfmisc_1 @ 
% 1.96/2.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.96/2.18      inference('demod', [status(thm)], ['4', '35'])).
% 1.96/2.18  thf(d3_struct_0, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.96/2.18  thf('37', plain,
% 1.96/2.18      (![X3 : $i]:
% 1.96/2.18         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.96/2.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.96/2.18  thf('38', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['12', '27', '28', '33', '34'])).
% 1.96/2.18  thf('39', plain,
% 1.96/2.18      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 1.96/2.18      inference('sup+', [status(thm)], ['37', '38'])).
% 1.96/2.18  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['31', '32'])).
% 1.96/2.18  thf(dt_l1_pre_topc, axiom,
% 1.96/2.18    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.96/2.18  thf('41', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.96/2.18  thf('42', plain, ((l1_struct_0 @ sk_D)),
% 1.96/2.18      inference('sup-', [status(thm)], ['40', '41'])).
% 1.96/2.18  thf('43', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['39', '42'])).
% 1.96/2.18  thf('44', plain,
% 1.96/2.18      (![X3 : $i]:
% 1.96/2.18         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.96/2.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.96/2.18  thf('45', plain,
% 1.96/2.18      (![X3 : $i]:
% 1.96/2.18         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.96/2.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.96/2.18  thf('46', plain,
% 1.96/2.18      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('47', plain,
% 1.96/2.18      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 1.96/2.18        | ~ (l1_struct_0 @ sk_C))),
% 1.96/2.18      inference('sup+', [status(thm)], ['45', '46'])).
% 1.96/2.18  thf('48', plain, ((l1_pre_topc @ sk_C)),
% 1.96/2.18      inference('demod', [status(thm)], ['24', '25'])).
% 1.96/2.18  thf('49', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.96/2.18  thf('50', plain, ((l1_struct_0 @ sk_C)),
% 1.96/2.18      inference('sup-', [status(thm)], ['48', '49'])).
% 1.96/2.18  thf('51', plain,
% 1.96/2.18      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['47', '50'])).
% 1.96/2.18  thf('52', plain,
% 1.96/2.18      (![X1 : $i, X2 : $i]:
% 1.96/2.18         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.96/2.18          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.96/2.18          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.96/2.18      inference('simplify', [status(thm)], ['10'])).
% 1.96/2.18  thf('53', plain,
% 1.96/2.18      ((~ (v1_pre_topc @ sk_D)
% 1.96/2.18        | ~ (l1_pre_topc @ 
% 1.96/2.18             (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.96/2.18        | ((u1_struct_0 @ 
% 1.96/2.18            (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.96/2.18            = (k2_struct_0 @ sk_C)))),
% 1.96/2.18      inference('sup-', [status(thm)], ['51', '52'])).
% 1.96/2.18  thf('54', plain, ((v1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['15', '21', '26'])).
% 1.96/2.18  thf('55', plain,
% 1.96/2.18      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['47', '50'])).
% 1.96/2.18  thf('56', plain, ((l1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['31', '32'])).
% 1.96/2.18  thf('57', plain,
% 1.96/2.18      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['47', '50'])).
% 1.96/2.18  thf('58', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 1.96/2.18  thf('59', plain,
% 1.96/2.18      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 1.96/2.18      inference('sup+', [status(thm)], ['44', '58'])).
% 1.96/2.18  thf('60', plain, ((l1_struct_0 @ sk_D)),
% 1.96/2.18      inference('sup-', [status(thm)], ['40', '41'])).
% 1.96/2.18  thf('61', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['59', '60'])).
% 1.96/2.18  thf('62', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['43', '61'])).
% 1.96/2.18  thf('63', plain,
% 1.96/2.18      ((m1_subset_1 @ sk_E @ 
% 1.96/2.18        (k1_zfmisc_1 @ 
% 1.96/2.18         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.96/2.18      inference('demod', [status(thm)], ['36', '62'])).
% 1.96/2.18  thf('64', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 1.96/2.18  thf(t86_tmap_1, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.96/2.18       ( ![B:$i]:
% 1.96/2.18         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.96/2.18             ( l1_pre_topc @ B ) ) =>
% 1.96/2.18           ( ![C:$i]:
% 1.96/2.18             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.96/2.18               ( ![D:$i]:
% 1.96/2.18                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.96/2.18                   ( ![E:$i]:
% 1.96/2.18                     ( ( ( v1_funct_1 @ E ) & 
% 1.96/2.18                         ( v1_funct_2 @
% 1.96/2.18                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.96/2.18                         ( m1_subset_1 @
% 1.96/2.18                           E @ 
% 1.96/2.18                           ( k1_zfmisc_1 @
% 1.96/2.18                             ( k2_zfmisc_1 @
% 1.96/2.18                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.96/2.18                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.96/2.18                         ( ![F:$i]:
% 1.96/2.18                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.96/2.18                             ( ![G:$i]:
% 1.96/2.18                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.96/2.18                                 ( ( ( F ) = ( G ) ) =>
% 1.96/2.18                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.96/2.18                                     ( r1_tmap_1 @
% 1.96/2.18                                       C @ B @ 
% 1.96/2.18                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.96/2.18  thf('65', plain,
% 1.96/2.18      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.96/2.18         ((v2_struct_0 @ X25)
% 1.96/2.18          | ~ (v2_pre_topc @ X25)
% 1.96/2.18          | ~ (l1_pre_topc @ X25)
% 1.96/2.18          | (v2_struct_0 @ X26)
% 1.96/2.18          | ~ (m1_pre_topc @ X26 @ X27)
% 1.96/2.18          | ~ (v1_tsep_1 @ X28 @ X26)
% 1.96/2.18          | ~ (m1_pre_topc @ X28 @ X26)
% 1.96/2.18          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 1.96/2.18          | ((X29) != (X30))
% 1.96/2.18          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 1.96/2.18               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 1.96/2.18          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X29)
% 1.96/2.18          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 1.96/2.18          | ~ (m1_subset_1 @ X31 @ 
% 1.96/2.18               (k1_zfmisc_1 @ 
% 1.96/2.18                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.96/2.18          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.96/2.18          | ~ (v1_funct_1 @ X31)
% 1.96/2.18          | ~ (m1_pre_topc @ X28 @ X27)
% 1.96/2.18          | (v2_struct_0 @ X28)
% 1.96/2.18          | ~ (l1_pre_topc @ X27)
% 1.96/2.18          | ~ (v2_pre_topc @ X27)
% 1.96/2.18          | (v2_struct_0 @ X27))),
% 1.96/2.18      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.96/2.18  thf('66', plain,
% 1.96/2.18      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 1.96/2.18         ((v2_struct_0 @ X27)
% 1.96/2.18          | ~ (v2_pre_topc @ X27)
% 1.96/2.18          | ~ (l1_pre_topc @ X27)
% 1.96/2.18          | (v2_struct_0 @ X28)
% 1.96/2.18          | ~ (m1_pre_topc @ X28 @ X27)
% 1.96/2.18          | ~ (v1_funct_1 @ X31)
% 1.96/2.18          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.96/2.18          | ~ (m1_subset_1 @ X31 @ 
% 1.96/2.18               (k1_zfmisc_1 @ 
% 1.96/2.18                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.96/2.18          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 1.96/2.18          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 1.96/2.18          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 1.96/2.18               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 1.96/2.18          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 1.96/2.18          | ~ (m1_pre_topc @ X28 @ X26)
% 1.96/2.18          | ~ (v1_tsep_1 @ X28 @ X26)
% 1.96/2.18          | ~ (m1_pre_topc @ X26 @ X27)
% 1.96/2.18          | (v2_struct_0 @ X26)
% 1.96/2.18          | ~ (l1_pre_topc @ X25)
% 1.96/2.18          | ~ (v2_pre_topc @ X25)
% 1.96/2.18          | (v2_struct_0 @ X25))),
% 1.96/2.18      inference('simplify', [status(thm)], ['65'])).
% 1.96/2.18  thf('67', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ X1 @ 
% 1.96/2.18             (k1_zfmisc_1 @ 
% 1.96/2.18              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.96/2.18          | (v2_struct_0 @ X0)
% 1.96/2.18          | ~ (v2_pre_topc @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | (v2_struct_0 @ sk_D)
% 1.96/2.18          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.96/2.18          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 1.96/2.18          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.96/2.18          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 1.96/2.18          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.96/2.18               X4)
% 1.96/2.18          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 1.96/2.18          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.96/2.18          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.96/2.18          | ~ (v1_funct_1 @ X1)
% 1.96/2.18          | ~ (m1_pre_topc @ X3 @ X2)
% 1.96/2.18          | (v2_struct_0 @ X3)
% 1.96/2.18          | ~ (l1_pre_topc @ X2)
% 1.96/2.18          | ~ (v2_pre_topc @ X2)
% 1.96/2.18          | (v2_struct_0 @ X2))),
% 1.96/2.18      inference('sup-', [status(thm)], ['64', '66'])).
% 1.96/2.18  thf('68', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 1.96/2.18  thf('69', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 1.96/2.18  thf('70', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ X1 @ 
% 1.96/2.18             (k1_zfmisc_1 @ 
% 1.96/2.18              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.96/2.18          | (v2_struct_0 @ X0)
% 1.96/2.18          | ~ (v2_pre_topc @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | (v2_struct_0 @ sk_D)
% 1.96/2.18          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.96/2.18          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 1.96/2.18          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.96/2.18          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 1.96/2.18          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.96/2.18               X4)
% 1.96/2.18          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 1.96/2.18          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.96/2.18          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.96/2.18          | ~ (v1_funct_1 @ X1)
% 1.96/2.18          | ~ (m1_pre_topc @ X3 @ X2)
% 1.96/2.18          | (v2_struct_0 @ X3)
% 1.96/2.18          | ~ (l1_pre_topc @ X2)
% 1.96/2.18          | ~ (v2_pre_topc @ X2)
% 1.96/2.18          | (v2_struct_0 @ X2))),
% 1.96/2.18      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.96/2.18  thf('71', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         ((v2_struct_0 @ X0)
% 1.96/2.18          | ~ (v2_pre_topc @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | (v2_struct_0 @ X1)
% 1.96/2.18          | ~ (m1_pre_topc @ X1 @ X0)
% 1.96/2.18          | ~ (v1_funct_1 @ sk_E)
% 1.96/2.18          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.96/2.18          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.96/2.18          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.96/2.18          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.96/2.18               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.96/2.18          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 1.96/2.18          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.96/2.18          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.96/2.18          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.96/2.18          | (v2_struct_0 @ sk_D)
% 1.96/2.18          | ~ (l1_pre_topc @ sk_B)
% 1.96/2.18          | ~ (v2_pre_topc @ sk_B)
% 1.96/2.18          | (v2_struct_0 @ sk_B))),
% 1.96/2.18      inference('sup-', [status(thm)], ['63', '70'])).
% 1.96/2.18  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('73', plain,
% 1.96/2.18      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('74', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['12', '27', '28', '33', '34'])).
% 1.96/2.18  thf('75', plain,
% 1.96/2.18      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.96/2.18      inference('demod', [status(thm)], ['73', '74'])).
% 1.96/2.18  thf('76', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['43', '61'])).
% 1.96/2.18  thf('77', plain,
% 1.96/2.18      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.96/2.18      inference('demod', [status(thm)], ['75', '76'])).
% 1.96/2.18  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('80', plain,
% 1.96/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.18         ((v2_struct_0 @ X0)
% 1.96/2.18          | ~ (v2_pre_topc @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | (v2_struct_0 @ X1)
% 1.96/2.18          | ~ (m1_pre_topc @ X1 @ X0)
% 1.96/2.18          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.96/2.18          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.96/2.18          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.96/2.18               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.96/2.18          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 1.96/2.18          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.96/2.18          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.96/2.18          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.96/2.18          | (v2_struct_0 @ sk_D)
% 1.96/2.18          | (v2_struct_0 @ sk_B))),
% 1.96/2.18      inference('demod', [status(thm)], ['71', '72', '77', '78', '79'])).
% 1.96/2.18  thf('81', plain,
% 1.96/2.18      (((v2_struct_0 @ sk_B)
% 1.96/2.18        | (v2_struct_0 @ sk_D)
% 1.96/2.18        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.96/2.18        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.96/2.18        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.96/2.18        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.96/2.18        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.96/2.18        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.96/2.18        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.96/2.18        | (v2_struct_0 @ sk_C)
% 1.96/2.18        | ~ (l1_pre_topc @ sk_A)
% 1.96/2.18        | ~ (v2_pre_topc @ sk_A)
% 1.96/2.18        | (v2_struct_0 @ sk_A))),
% 1.96/2.18      inference('sup-', [status(thm)], ['3', '80'])).
% 1.96/2.18  thf('82', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('83', plain,
% 1.96/2.18      (![X3 : $i]:
% 1.96/2.18         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.96/2.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.96/2.18  thf(t2_tsep_1, axiom,
% 1.96/2.18    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.96/2.18  thf('84', plain,
% 1.96/2.18      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 1.96/2.18      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.96/2.18  thf(t1_tsep_1, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( l1_pre_topc @ A ) =>
% 1.96/2.18       ( ![B:$i]:
% 1.96/2.18         ( ( m1_pre_topc @ B @ A ) =>
% 1.96/2.18           ( m1_subset_1 @
% 1.96/2.18             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.96/2.18  thf('85', plain,
% 1.96/2.18      (![X19 : $i, X20 : $i]:
% 1.96/2.18         (~ (m1_pre_topc @ X19 @ X20)
% 1.96/2.18          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 1.96/2.18             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.96/2.18          | ~ (l1_pre_topc @ X20))),
% 1.96/2.18      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.96/2.18  thf('86', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (l1_pre_topc @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.96/2.18             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.96/2.18      inference('sup-', [status(thm)], ['84', '85'])).
% 1.96/2.18  thf('87', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.96/2.18           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.96/2.18          | ~ (l1_pre_topc @ X0))),
% 1.96/2.18      inference('simplify', [status(thm)], ['86'])).
% 1.96/2.18  thf('88', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.96/2.18           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.96/2.18          | ~ (l1_struct_0 @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0))),
% 1.96/2.18      inference('sup+', [status(thm)], ['83', '87'])).
% 1.96/2.18  thf('89', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.96/2.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.96/2.18  thf('90', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (l1_pre_topc @ X0)
% 1.96/2.18          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.96/2.18             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.96/2.18      inference('clc', [status(thm)], ['88', '89'])).
% 1.96/2.18  thf('91', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 1.96/2.18  thf(t16_tsep_1, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.96/2.18       ( ![B:$i]:
% 1.96/2.18         ( ( m1_pre_topc @ B @ A ) =>
% 1.96/2.18           ( ![C:$i]:
% 1.96/2.18             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.96/2.18               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.96/2.18                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.96/2.18                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.96/2.18  thf('92', plain,
% 1.96/2.18      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.96/2.18         (~ (m1_pre_topc @ X16 @ X17)
% 1.96/2.18          | ((X18) != (u1_struct_0 @ X16))
% 1.96/2.18          | ~ (v3_pre_topc @ X18 @ X17)
% 1.96/2.18          | (v1_tsep_1 @ X16 @ X17)
% 1.96/2.18          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.96/2.18          | ~ (l1_pre_topc @ X17)
% 1.96/2.18          | ~ (v2_pre_topc @ X17))),
% 1.96/2.18      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.96/2.18  thf('93', plain,
% 1.96/2.18      (![X16 : $i, X17 : $i]:
% 1.96/2.18         (~ (v2_pre_topc @ X17)
% 1.96/2.18          | ~ (l1_pre_topc @ X17)
% 1.96/2.18          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 1.96/2.18               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.96/2.18          | (v1_tsep_1 @ X16 @ X17)
% 1.96/2.18          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 1.96/2.18          | ~ (m1_pre_topc @ X16 @ X17))),
% 1.96/2.18      inference('simplify', [status(thm)], ['92'])).
% 1.96/2.18  thf('94', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.96/2.18             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.96/2.18          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.96/2.18          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.96/2.18          | (v1_tsep_1 @ X0 @ sk_D)
% 1.96/2.18          | ~ (l1_pre_topc @ sk_D)
% 1.96/2.18          | ~ (v2_pre_topc @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['91', '93'])).
% 1.96/2.18  thf('95', plain, ((l1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['31', '32'])).
% 1.96/2.18  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('97', plain,
% 1.96/2.18      (![X1 : $i, X2 : $i]:
% 1.96/2.18         (~ (m1_pre_topc @ X1 @ X2)
% 1.96/2.18          | (v2_pre_topc @ X1)
% 1.96/2.18          | ~ (l1_pre_topc @ X2)
% 1.96/2.18          | ~ (v2_pre_topc @ X2))),
% 1.96/2.18      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.96/2.18  thf('98', plain,
% 1.96/2.18      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['96', '97'])).
% 1.96/2.18  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('101', plain, ((v2_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.96/2.18  thf('102', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.96/2.18             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.96/2.18          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.96/2.18          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.96/2.18          | (v1_tsep_1 @ X0 @ sk_D))),
% 1.96/2.18      inference('demod', [status(thm)], ['94', '95', '101'])).
% 1.96/2.18  thf('103', plain,
% 1.96/2.18      ((~ (l1_pre_topc @ sk_C)
% 1.96/2.18        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.96/2.18        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.96/2.18        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 1.96/2.18      inference('sup-', [status(thm)], ['90', '102'])).
% 1.96/2.18  thf('104', plain, ((l1_pre_topc @ sk_C)),
% 1.96/2.18      inference('demod', [status(thm)], ['24', '25'])).
% 1.96/2.18  thf('105', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['43', '61'])).
% 1.96/2.18  thf('106', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['59', '60'])).
% 1.96/2.18  thf(fc10_tops_1, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.96/2.18       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.96/2.18  thf('107', plain,
% 1.96/2.18      (![X15 : $i]:
% 1.96/2.18         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 1.96/2.18          | ~ (l1_pre_topc @ X15)
% 1.96/2.18          | ~ (v2_pre_topc @ X15))),
% 1.96/2.18      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.96/2.18  thf('108', plain,
% 1.96/2.18      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 1.96/2.18        | ~ (v2_pre_topc @ sk_D)
% 1.96/2.18        | ~ (l1_pre_topc @ sk_D))),
% 1.96/2.18      inference('sup+', [status(thm)], ['106', '107'])).
% 1.96/2.18  thf('109', plain, ((v2_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.96/2.18  thf('110', plain, ((l1_pre_topc @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['31', '32'])).
% 1.96/2.18  thf('111', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['108', '109', '110'])).
% 1.96/2.18  thf('112', plain,
% 1.96/2.18      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('113', plain,
% 1.96/2.18      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 1.96/2.18      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.96/2.18  thf(t65_pre_topc, axiom,
% 1.96/2.18    (![A:$i]:
% 1.96/2.18     ( ( l1_pre_topc @ A ) =>
% 1.96/2.18       ( ![B:$i]:
% 1.96/2.18         ( ( l1_pre_topc @ B ) =>
% 1.96/2.18           ( ( m1_pre_topc @ A @ B ) <=>
% 1.96/2.18             ( m1_pre_topc @
% 1.96/2.18               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.96/2.18  thf('114', plain,
% 1.96/2.18      (![X13 : $i, X14 : $i]:
% 1.96/2.18         (~ (l1_pre_topc @ X13)
% 1.96/2.18          | ~ (m1_pre_topc @ X14 @ X13)
% 1.96/2.18          | (m1_pre_topc @ X14 @ 
% 1.96/2.18             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 1.96/2.18          | ~ (l1_pre_topc @ X14))),
% 1.96/2.18      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.96/2.18  thf('115', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         (~ (l1_pre_topc @ X0)
% 1.96/2.18          | ~ (l1_pre_topc @ X0)
% 1.96/2.18          | (m1_pre_topc @ X0 @ 
% 1.96/2.18             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.96/2.18          | ~ (l1_pre_topc @ X0))),
% 1.96/2.18      inference('sup-', [status(thm)], ['113', '114'])).
% 1.96/2.18  thf('116', plain,
% 1.96/2.18      (![X0 : $i]:
% 1.96/2.18         ((m1_pre_topc @ X0 @ 
% 1.96/2.18           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.96/2.18          | ~ (l1_pre_topc @ X0))),
% 1.96/2.18      inference('simplify', [status(thm)], ['115'])).
% 1.96/2.18  thf('117', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 1.96/2.18      inference('sup+', [status(thm)], ['112', '116'])).
% 1.96/2.18  thf('118', plain, ((l1_pre_topc @ sk_C)),
% 1.96/2.18      inference('demod', [status(thm)], ['24', '25'])).
% 1.96/2.18  thf('119', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['117', '118'])).
% 1.96/2.18  thf('120', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['103', '104', '105', '111', '119'])).
% 1.96/2.18  thf('121', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.96/2.18      inference('demod', [status(thm)], ['117', '118'])).
% 1.96/2.18  thf('122', plain,
% 1.96/2.18      (![X3 : $i]:
% 1.96/2.18         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.96/2.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.96/2.18  thf('123', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('124', plain, (((sk_F) = (sk_G))),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('125', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['123', '124'])).
% 1.96/2.18  thf('126', plain,
% 1.96/2.18      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 1.96/2.18      inference('sup+', [status(thm)], ['122', '125'])).
% 1.96/2.18  thf('127', plain, ((l1_struct_0 @ sk_C)),
% 1.96/2.18      inference('sup-', [status(thm)], ['48', '49'])).
% 1.96/2.18  thf('128', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['126', '127'])).
% 1.96/2.18  thf('129', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['43', '61'])).
% 1.96/2.18  thf('130', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.96/2.18      inference('demod', [status(thm)], ['126', '127'])).
% 1.96/2.18  thf('131', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('134', plain,
% 1.96/2.18      (((v2_struct_0 @ sk_B)
% 1.96/2.18        | (v2_struct_0 @ sk_D)
% 1.96/2.18        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.96/2.18        | (v2_struct_0 @ sk_C)
% 1.96/2.18        | (v2_struct_0 @ sk_A))),
% 1.96/2.18      inference('demod', [status(thm)],
% 1.96/2.18                ['81', '82', '120', '121', '128', '129', '130', '131', '132', 
% 1.96/2.18                 '133'])).
% 1.96/2.18  thf('135', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('136', plain,
% 1.96/2.18      (((v2_struct_0 @ sk_A)
% 1.96/2.18        | (v2_struct_0 @ sk_C)
% 1.96/2.18        | (v2_struct_0 @ sk_D)
% 1.96/2.18        | (v2_struct_0 @ sk_B))),
% 1.96/2.18      inference('sup-', [status(thm)], ['134', '135'])).
% 1.96/2.18  thf('137', plain, (~ (v2_struct_0 @ sk_D)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('138', plain,
% 1.96/2.18      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.96/2.18      inference('sup-', [status(thm)], ['136', '137'])).
% 1.96/2.18  thf('139', plain, (~ (v2_struct_0 @ sk_B)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('140', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.96/2.18      inference('clc', [status(thm)], ['138', '139'])).
% 1.96/2.18  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 1.96/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.18  thf('142', plain, ((v2_struct_0 @ sk_C)),
% 1.96/2.18      inference('clc', [status(thm)], ['140', '141'])).
% 1.96/2.18  thf('143', plain, ($false), inference('demod', [status(thm)], ['0', '142'])).
% 1.96/2.18  
% 1.96/2.18  % SZS output end Refutation
% 1.96/2.18  
% 1.96/2.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
