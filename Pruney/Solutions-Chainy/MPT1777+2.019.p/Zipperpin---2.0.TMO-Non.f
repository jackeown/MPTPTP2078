%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s0gBGEbT5Y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:29 EST 2020

% Result     : Timeout 58.19s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  183 (1538 expanded)
%              Number of leaves         :   41 ( 467 expanded)
%              Depth                    :   22
%              Number of atoms          : 1601 (40526 expanded)
%              Number of equality atoms :   60 (1384 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_pre_topc @ X10 @ X11 )
       != ( g1_pre_topc @ X8 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13','18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','27'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('31',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('49',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['39','46'])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('52',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['39','46'])).

thf('53',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ( ( u1_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['36','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_tsep_1 @ X29 @ X27 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ( X30 != X31 )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('63',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X31 )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( v1_tsep_1 @ X29 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
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
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

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
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('72',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','58'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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
    inference(demod,[status(thm)],['68','69','74','75','76'])).

thf('78',plain,
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
    inference('sup-',[status(thm)],['3','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('81',plain,(
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

thf('82',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('89',plain,(
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

thf('90',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('93',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('94',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('95',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['91','92','98'])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['87','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('102',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','58'])).

thf('103',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('104',plain,(
    ! [X14: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('105',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('107',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('108',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
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

thf('111',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['109','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('116',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['100','101','102','108','116'])).

thf('118',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['114','115'])).

thf('119',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','58'])).

thf('127',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('128',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','117','118','125','126','127','128','129','130'])).

thf('132',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s0gBGEbT5Y
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:12:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 58.19/58.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 58.19/58.39  % Solved by: fo/fo7.sh
% 58.19/58.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.19/58.39  % done 20065 iterations in 57.920s
% 58.19/58.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 58.19/58.39  % SZS output start Refutation
% 58.19/58.39  thf(sk_C_type, type, sk_C: $i).
% 58.19/58.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 58.19/58.39  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 58.19/58.39  thf(sk_B_type, type, sk_B: $i).
% 58.19/58.39  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 58.19/58.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 58.19/58.39  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 58.19/58.39  thf(sk_A_type, type, sk_A: $i).
% 58.19/58.39  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 58.19/58.39  thf(sk_E_type, type, sk_E: $i).
% 58.19/58.39  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 58.19/58.39  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 58.19/58.39  thf(sk_F_type, type, sk_F: $i).
% 58.19/58.39  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 58.19/58.39  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 58.19/58.39  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 58.19/58.39  thf(sk_D_type, type, sk_D: $i).
% 58.19/58.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 58.19/58.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 58.19/58.39  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 58.19/58.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 58.19/58.39  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 58.19/58.39  thf(sk_G_type, type, sk_G: $i).
% 58.19/58.39  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 58.19/58.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 58.19/58.39  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 58.19/58.39  thf(t88_tmap_1, conjecture,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 58.19/58.39       ( ![B:$i]:
% 58.19/58.39         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 58.19/58.39             ( l1_pre_topc @ B ) ) =>
% 58.19/58.39           ( ![C:$i]:
% 58.19/58.39             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 58.19/58.39               ( ![D:$i]:
% 58.19/58.39                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 58.19/58.39                   ( ![E:$i]:
% 58.19/58.39                     ( ( ( v1_funct_1 @ E ) & 
% 58.19/58.39                         ( v1_funct_2 @
% 58.19/58.39                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 58.19/58.39                         ( m1_subset_1 @
% 58.19/58.39                           E @ 
% 58.19/58.39                           ( k1_zfmisc_1 @
% 58.19/58.39                             ( k2_zfmisc_1 @
% 58.19/58.39                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 58.19/58.39                       ( ( ( g1_pre_topc @
% 58.19/58.39                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 58.19/58.39                           ( D ) ) =>
% 58.19/58.39                         ( ![F:$i]:
% 58.19/58.39                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 58.19/58.39                             ( ![G:$i]:
% 58.19/58.39                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 58.19/58.39                                 ( ( ( ( F ) = ( G ) ) & 
% 58.19/58.39                                     ( r1_tmap_1 @
% 58.19/58.39                                       C @ B @ 
% 58.19/58.39                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 58.19/58.39                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 58.19/58.39  thf(zf_stmt_0, negated_conjecture,
% 58.19/58.39    (~( ![A:$i]:
% 58.19/58.39        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 58.19/58.39            ( l1_pre_topc @ A ) ) =>
% 58.19/58.39          ( ![B:$i]:
% 58.19/58.39            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 58.19/58.39                ( l1_pre_topc @ B ) ) =>
% 58.19/58.39              ( ![C:$i]:
% 58.19/58.39                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 58.19/58.39                  ( ![D:$i]:
% 58.19/58.39                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 58.19/58.39                      ( ![E:$i]:
% 58.19/58.39                        ( ( ( v1_funct_1 @ E ) & 
% 58.19/58.39                            ( v1_funct_2 @
% 58.19/58.39                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 58.19/58.39                            ( m1_subset_1 @
% 58.19/58.39                              E @ 
% 58.19/58.39                              ( k1_zfmisc_1 @
% 58.19/58.39                                ( k2_zfmisc_1 @
% 58.19/58.39                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 58.19/58.39                          ( ( ( g1_pre_topc @
% 58.19/58.39                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 58.19/58.39                              ( D ) ) =>
% 58.19/58.39                            ( ![F:$i]:
% 58.19/58.39                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 58.19/58.39                                ( ![G:$i]:
% 58.19/58.39                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 58.19/58.39                                    ( ( ( ( F ) = ( G ) ) & 
% 58.19/58.39                                        ( r1_tmap_1 @
% 58.19/58.39                                          C @ B @ 
% 58.19/58.39                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 58.19/58.39                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 58.19/58.39    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 58.19/58.39  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('1', plain,
% 58.19/58.39      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 58.19/58.39        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('2', plain, (((sk_F) = (sk_G))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('3', plain,
% 58.19/58.39      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 58.19/58.39        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 58.19/58.39      inference('demod', [status(thm)], ['1', '2'])).
% 58.19/58.39  thf('4', plain,
% 58.19/58.39      ((m1_subset_1 @ sk_E @ 
% 58.19/58.39        (k1_zfmisc_1 @ 
% 58.19/58.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('5', plain,
% 58.19/58.39      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf(abstractness_v1_pre_topc, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_pre_topc @ A ) =>
% 58.19/58.39       ( ( v1_pre_topc @ A ) =>
% 58.19/58.39         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 58.19/58.39  thf('6', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         (~ (v1_pre_topc @ X0)
% 58.19/58.39          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 58.19/58.39          | ~ (l1_pre_topc @ X0))),
% 58.19/58.39      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 58.19/58.39  thf(dt_u1_pre_topc, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_pre_topc @ A ) =>
% 58.19/58.39       ( m1_subset_1 @
% 58.19/58.39         ( u1_pre_topc @ A ) @ 
% 58.19/58.39         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 58.19/58.39  thf('7', plain,
% 58.19/58.39      (![X7 : $i]:
% 58.19/58.39         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 58.19/58.39           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 58.19/58.39          | ~ (l1_pre_topc @ X7))),
% 58.19/58.39      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 58.19/58.39  thf(free_g1_pre_topc, axiom,
% 58.19/58.39    (![A:$i,B:$i]:
% 58.19/58.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 58.19/58.39       ( ![C:$i,D:$i]:
% 58.19/58.39         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 58.19/58.39           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 58.19/58.39  thf('8', plain,
% 58.19/58.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 58.19/58.39         (((g1_pre_topc @ X10 @ X11) != (g1_pre_topc @ X8 @ X9))
% 58.19/58.39          | ((X10) = (X8))
% 58.19/58.39          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 58.19/58.39      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 58.19/58.39  thf('9', plain,
% 58.19/58.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.19/58.39         (~ (l1_pre_topc @ X0)
% 58.19/58.39          | ((u1_struct_0 @ X0) = (X1))
% 58.19/58.39          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 58.19/58.39              != (g1_pre_topc @ X1 @ X2)))),
% 58.19/58.39      inference('sup-', [status(thm)], ['7', '8'])).
% 58.19/58.39  thf('10', plain,
% 58.19/58.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.19/58.39         (((X0) != (g1_pre_topc @ X2 @ X1))
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | ~ (v1_pre_topc @ X0)
% 58.19/58.39          | ((u1_struct_0 @ X0) = (X2))
% 58.19/58.39          | ~ (l1_pre_topc @ X0))),
% 58.19/58.39      inference('sup-', [status(thm)], ['6', '9'])).
% 58.19/58.39  thf('11', plain,
% 58.19/58.39      (![X1 : $i, X2 : $i]:
% 58.19/58.39         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 58.19/58.39          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 58.19/58.39          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 58.19/58.39      inference('simplify', [status(thm)], ['10'])).
% 58.19/58.39  thf('12', plain,
% 58.19/58.39      ((~ (v1_pre_topc @ sk_D)
% 58.19/58.39        | ~ (l1_pre_topc @ 
% 58.19/58.39             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 58.19/58.39        | ((u1_struct_0 @ 
% 58.19/58.39            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 58.19/58.39            = (u1_struct_0 @ sk_C)))),
% 58.19/58.39      inference('sup-', [status(thm)], ['5', '11'])).
% 58.19/58.39  thf('13', plain,
% 58.19/58.39      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf(dt_m1_pre_topc, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_pre_topc @ A ) =>
% 58.19/58.39       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 58.19/58.39  thf('15', plain,
% 58.19/58.39      (![X5 : $i, X6 : $i]:
% 58.19/58.39         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 58.19/58.39      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 58.19/58.39  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 58.19/58.39      inference('sup-', [status(thm)], ['14', '15'])).
% 58.19/58.39  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('18', plain, ((l1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['16', '17'])).
% 58.19/58.39  thf('19', plain,
% 58.19/58.39      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('20', plain,
% 58.19/58.39      ((~ (v1_pre_topc @ sk_D) | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 58.19/58.39      inference('demod', [status(thm)], ['12', '13', '18', '19'])).
% 58.19/58.39  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf(t11_tmap_1, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_pre_topc @ A ) =>
% 58.19/58.39       ( ![B:$i]:
% 58.19/58.39         ( ( m1_pre_topc @ B @ A ) =>
% 58.19/58.39           ( ( v1_pre_topc @
% 58.19/58.39               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 58.19/58.39             ( m1_pre_topc @
% 58.19/58.39               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 58.19/58.39  thf('22', plain,
% 58.19/58.39      (![X15 : $i, X16 : $i]:
% 58.19/58.39         (~ (m1_pre_topc @ X15 @ X16)
% 58.19/58.39          | (v1_pre_topc @ 
% 58.19/58.39             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 58.19/58.39          | ~ (l1_pre_topc @ X16))),
% 58.19/58.39      inference('cnf', [status(esa)], [t11_tmap_1])).
% 58.19/58.39  thf('23', plain,
% 58.19/58.39      ((~ (l1_pre_topc @ sk_A)
% 58.19/58.39        | (v1_pre_topc @ 
% 58.19/58.39           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 58.19/58.39      inference('sup-', [status(thm)], ['21', '22'])).
% 58.19/58.39  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('25', plain,
% 58.19/58.39      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('26', plain, ((v1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 58.19/58.39  thf('27', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['20', '26'])).
% 58.19/58.39  thf('28', plain,
% 58.19/58.39      ((m1_subset_1 @ sk_E @ 
% 58.19/58.39        (k1_zfmisc_1 @ 
% 58.19/58.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 58.19/58.39      inference('demod', [status(thm)], ['4', '27'])).
% 58.19/58.39  thf(d3_struct_0, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 58.19/58.39  thf('29', plain,
% 58.19/58.39      (![X3 : $i]:
% 58.19/58.39         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 58.19/58.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 58.19/58.39  thf('30', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['20', '26'])).
% 58.19/58.39  thf('31', plain,
% 58.19/58.39      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 58.19/58.39      inference('sup+', [status(thm)], ['29', '30'])).
% 58.19/58.39  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['16', '17'])).
% 58.19/58.39  thf(dt_l1_pre_topc, axiom,
% 58.19/58.39    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 58.19/58.39  thf('33', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 58.19/58.39      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 58.19/58.39  thf('34', plain, ((l1_struct_0 @ sk_D)),
% 58.19/58.39      inference('sup-', [status(thm)], ['32', '33'])).
% 58.19/58.39  thf('35', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['31', '34'])).
% 58.19/58.39  thf('36', plain,
% 58.19/58.39      (![X3 : $i]:
% 58.19/58.39         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 58.19/58.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 58.19/58.39  thf('37', plain,
% 58.19/58.39      (![X3 : $i]:
% 58.19/58.39         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 58.19/58.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 58.19/58.39  thf('38', plain,
% 58.19/58.39      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('39', plain,
% 58.19/58.39      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 58.19/58.39        | ~ (l1_struct_0 @ sk_C))),
% 58.19/58.39      inference('sup+', [status(thm)], ['37', '38'])).
% 58.19/58.39  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('41', plain,
% 58.19/58.39      (![X5 : $i, X6 : $i]:
% 58.19/58.39         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 58.19/58.39      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 58.19/58.39  thf('42', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 58.19/58.39      inference('sup-', [status(thm)], ['40', '41'])).
% 58.19/58.39  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 58.19/58.39      inference('demod', [status(thm)], ['42', '43'])).
% 58.19/58.39  thf('45', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 58.19/58.39      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 58.19/58.39  thf('46', plain, ((l1_struct_0 @ sk_C)),
% 58.19/58.39      inference('sup-', [status(thm)], ['44', '45'])).
% 58.19/58.39  thf('47', plain,
% 58.19/58.39      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('demod', [status(thm)], ['39', '46'])).
% 58.19/58.39  thf('48', plain,
% 58.19/58.39      (![X1 : $i, X2 : $i]:
% 58.19/58.39         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 58.19/58.39          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 58.19/58.39          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 58.19/58.39      inference('simplify', [status(thm)], ['10'])).
% 58.19/58.39  thf('49', plain,
% 58.19/58.39      ((~ (v1_pre_topc @ sk_D)
% 58.19/58.39        | ~ (l1_pre_topc @ 
% 58.19/58.39             (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 58.19/58.39        | ((u1_struct_0 @ 
% 58.19/58.39            (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 58.19/58.39            = (k2_struct_0 @ sk_C)))),
% 58.19/58.39      inference('sup-', [status(thm)], ['47', '48'])).
% 58.19/58.39  thf('50', plain,
% 58.19/58.39      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('demod', [status(thm)], ['39', '46'])).
% 58.19/58.39  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['16', '17'])).
% 58.19/58.39  thf('52', plain,
% 58.19/58.39      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('demod', [status(thm)], ['39', '46'])).
% 58.19/58.39  thf('53', plain,
% 58.19/58.39      ((~ (v1_pre_topc @ sk_D) | ((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)))),
% 58.19/58.39      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 58.19/58.39  thf('54', plain, ((v1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 58.19/58.39  thf('55', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['53', '54'])).
% 58.19/58.39  thf('56', plain,
% 58.19/58.39      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 58.19/58.39      inference('sup+', [status(thm)], ['36', '55'])).
% 58.19/58.39  thf('57', plain, ((l1_struct_0 @ sk_D)),
% 58.19/58.39      inference('sup-', [status(thm)], ['32', '33'])).
% 58.19/58.39  thf('58', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['56', '57'])).
% 58.19/58.39  thf('59', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['35', '58'])).
% 58.19/58.39  thf('60', plain,
% 58.19/58.39      ((m1_subset_1 @ sk_E @ 
% 58.19/58.39        (k1_zfmisc_1 @ 
% 58.19/58.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 58.19/58.39      inference('demod', [status(thm)], ['28', '59'])).
% 58.19/58.39  thf('61', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['53', '54'])).
% 58.19/58.39  thf(t86_tmap_1, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 58.19/58.39       ( ![B:$i]:
% 58.19/58.39         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 58.19/58.39             ( l1_pre_topc @ B ) ) =>
% 58.19/58.39           ( ![C:$i]:
% 58.19/58.39             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 58.19/58.39               ( ![D:$i]:
% 58.19/58.39                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 58.19/58.39                   ( ![E:$i]:
% 58.19/58.39                     ( ( ( v1_funct_1 @ E ) & 
% 58.19/58.39                         ( v1_funct_2 @
% 58.19/58.39                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 58.19/58.39                         ( m1_subset_1 @
% 58.19/58.39                           E @ 
% 58.19/58.39                           ( k1_zfmisc_1 @
% 58.19/58.39                             ( k2_zfmisc_1 @
% 58.19/58.39                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 58.19/58.39                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 58.19/58.39                         ( ![F:$i]:
% 58.19/58.39                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 58.19/58.39                             ( ![G:$i]:
% 58.19/58.39                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 58.19/58.39                                 ( ( ( F ) = ( G ) ) =>
% 58.19/58.39                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 58.19/58.39                                     ( r1_tmap_1 @
% 58.19/58.39                                       C @ B @ 
% 58.19/58.39                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 58.19/58.39  thf('62', plain,
% 58.19/58.39      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 58.19/58.39         ((v2_struct_0 @ X26)
% 58.19/58.39          | ~ (v2_pre_topc @ X26)
% 58.19/58.39          | ~ (l1_pre_topc @ X26)
% 58.19/58.39          | (v2_struct_0 @ X27)
% 58.19/58.39          | ~ (m1_pre_topc @ X27 @ X28)
% 58.19/58.39          | ~ (v1_tsep_1 @ X29 @ X27)
% 58.19/58.39          | ~ (m1_pre_topc @ X29 @ X27)
% 58.19/58.39          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 58.19/58.39          | ((X30) != (X31))
% 58.19/58.39          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 58.19/58.39               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 58.19/58.39          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X30)
% 58.19/58.39          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 58.19/58.39          | ~ (m1_subset_1 @ X32 @ 
% 58.19/58.39               (k1_zfmisc_1 @ 
% 58.19/58.39                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 58.19/58.39          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 58.19/58.39          | ~ (v1_funct_1 @ X32)
% 58.19/58.39          | ~ (m1_pre_topc @ X29 @ X28)
% 58.19/58.39          | (v2_struct_0 @ X29)
% 58.19/58.39          | ~ (l1_pre_topc @ X28)
% 58.19/58.39          | ~ (v2_pre_topc @ X28)
% 58.19/58.39          | (v2_struct_0 @ X28))),
% 58.19/58.39      inference('cnf', [status(esa)], [t86_tmap_1])).
% 58.19/58.39  thf('63', plain,
% 58.19/58.39      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 58.19/58.39         ((v2_struct_0 @ X28)
% 58.19/58.39          | ~ (v2_pre_topc @ X28)
% 58.19/58.39          | ~ (l1_pre_topc @ X28)
% 58.19/58.39          | (v2_struct_0 @ X29)
% 58.19/58.39          | ~ (m1_pre_topc @ X29 @ X28)
% 58.19/58.39          | ~ (v1_funct_1 @ X32)
% 58.19/58.39          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 58.19/58.39          | ~ (m1_subset_1 @ X32 @ 
% 58.19/58.39               (k1_zfmisc_1 @ 
% 58.19/58.39                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 58.19/58.39          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 58.19/58.39          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X31)
% 58.19/58.39          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 58.19/58.39               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 58.19/58.39          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 58.19/58.39          | ~ (m1_pre_topc @ X29 @ X27)
% 58.19/58.39          | ~ (v1_tsep_1 @ X29 @ X27)
% 58.19/58.39          | ~ (m1_pre_topc @ X27 @ X28)
% 58.19/58.39          | (v2_struct_0 @ X27)
% 58.19/58.39          | ~ (l1_pre_topc @ X26)
% 58.19/58.39          | ~ (v2_pre_topc @ X26)
% 58.19/58.39          | (v2_struct_0 @ X26))),
% 58.19/58.39      inference('simplify', [status(thm)], ['62'])).
% 58.19/58.39  thf('64', plain,
% 58.19/58.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 58.19/58.39         (~ (m1_subset_1 @ X1 @ 
% 58.19/58.39             (k1_zfmisc_1 @ 
% 58.19/58.39              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 58.19/58.39          | (v2_struct_0 @ X0)
% 58.19/58.39          | ~ (v2_pre_topc @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | (v2_struct_0 @ sk_D)
% 58.19/58.39          | ~ (m1_pre_topc @ sk_D @ X2)
% 58.19/58.39          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 58.19/58.39          | ~ (m1_pre_topc @ X3 @ sk_D)
% 58.19/58.39          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 58.19/58.39          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 58.19/58.39               X4)
% 58.19/58.39          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 58.19/58.39          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 58.19/58.39          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 58.19/58.39          | ~ (v1_funct_1 @ X1)
% 58.19/58.39          | ~ (m1_pre_topc @ X3 @ X2)
% 58.19/58.39          | (v2_struct_0 @ X3)
% 58.19/58.39          | ~ (l1_pre_topc @ X2)
% 58.19/58.39          | ~ (v2_pre_topc @ X2)
% 58.19/58.39          | (v2_struct_0 @ X2))),
% 58.19/58.39      inference('sup-', [status(thm)], ['61', '63'])).
% 58.19/58.39  thf('65', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['53', '54'])).
% 58.19/58.39  thf('66', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['53', '54'])).
% 58.19/58.39  thf('67', plain,
% 58.19/58.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 58.19/58.39         (~ (m1_subset_1 @ X1 @ 
% 58.19/58.39             (k1_zfmisc_1 @ 
% 58.19/58.39              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 58.19/58.39          | (v2_struct_0 @ X0)
% 58.19/58.39          | ~ (v2_pre_topc @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | (v2_struct_0 @ sk_D)
% 58.19/58.39          | ~ (m1_pre_topc @ sk_D @ X2)
% 58.19/58.39          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 58.19/58.39          | ~ (m1_pre_topc @ X3 @ sk_D)
% 58.19/58.39          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 58.19/58.39          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 58.19/58.39               X4)
% 58.19/58.39          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 58.19/58.39          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 58.19/58.39          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 58.19/58.39          | ~ (v1_funct_1 @ X1)
% 58.19/58.39          | ~ (m1_pre_topc @ X3 @ X2)
% 58.19/58.39          | (v2_struct_0 @ X3)
% 58.19/58.39          | ~ (l1_pre_topc @ X2)
% 58.19/58.39          | ~ (v2_pre_topc @ X2)
% 58.19/58.39          | (v2_struct_0 @ X2))),
% 58.19/58.39      inference('demod', [status(thm)], ['64', '65', '66'])).
% 58.19/58.39  thf('68', plain,
% 58.19/58.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.19/58.39         ((v2_struct_0 @ X0)
% 58.19/58.39          | ~ (v2_pre_topc @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | (v2_struct_0 @ X1)
% 58.19/58.39          | ~ (m1_pre_topc @ X1 @ X0)
% 58.19/58.39          | ~ (v1_funct_1 @ sk_E)
% 58.19/58.39          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 58.19/58.39          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 58.19/58.39          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 58.19/58.39          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 58.19/58.39               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 58.19/58.39          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 58.19/58.39          | ~ (m1_pre_topc @ X1 @ sk_D)
% 58.19/58.39          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 58.19/58.39          | ~ (m1_pre_topc @ sk_D @ X0)
% 58.19/58.39          | (v2_struct_0 @ sk_D)
% 58.19/58.39          | ~ (l1_pre_topc @ sk_B)
% 58.19/58.39          | ~ (v2_pre_topc @ sk_B)
% 58.19/58.39          | (v2_struct_0 @ sk_B))),
% 58.19/58.39      inference('sup-', [status(thm)], ['60', '67'])).
% 58.19/58.39  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('70', plain,
% 58.19/58.39      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('71', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['20', '26'])).
% 58.19/58.39  thf('72', plain,
% 58.19/58.39      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 58.19/58.39      inference('demod', [status(thm)], ['70', '71'])).
% 58.19/58.39  thf('73', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['35', '58'])).
% 58.19/58.39  thf('74', plain,
% 58.19/58.39      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 58.19/58.39      inference('demod', [status(thm)], ['72', '73'])).
% 58.19/58.39  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('77', plain,
% 58.19/58.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.19/58.39         ((v2_struct_0 @ X0)
% 58.19/58.39          | ~ (v2_pre_topc @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | (v2_struct_0 @ X1)
% 58.19/58.39          | ~ (m1_pre_topc @ X1 @ X0)
% 58.19/58.39          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 58.19/58.39          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 58.19/58.39          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 58.19/58.39               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 58.19/58.39          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 58.19/58.39          | ~ (m1_pre_topc @ X1 @ sk_D)
% 58.19/58.39          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 58.19/58.39          | ~ (m1_pre_topc @ sk_D @ X0)
% 58.19/58.39          | (v2_struct_0 @ sk_D)
% 58.19/58.39          | (v2_struct_0 @ sk_B))),
% 58.19/58.39      inference('demod', [status(thm)], ['68', '69', '74', '75', '76'])).
% 58.19/58.39  thf('78', plain,
% 58.19/58.39      (((v2_struct_0 @ sk_B)
% 58.19/58.39        | (v2_struct_0 @ sk_D)
% 58.19/58.39        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 58.19/58.39        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 58.19/58.39        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 58.19/58.39        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 58.19/58.39        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 58.19/58.39        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 58.19/58.39        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 58.19/58.39        | (v2_struct_0 @ sk_C)
% 58.19/58.39        | ~ (l1_pre_topc @ sk_A)
% 58.19/58.39        | ~ (v2_pre_topc @ sk_A)
% 58.19/58.39        | (v2_struct_0 @ sk_A))),
% 58.19/58.39      inference('sup-', [status(thm)], ['3', '77'])).
% 58.19/58.39  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('80', plain,
% 58.19/58.39      (![X3 : $i]:
% 58.19/58.39         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 58.19/58.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 58.19/58.39  thf(t2_tsep_1, axiom,
% 58.19/58.39    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 58.19/58.39  thf('81', plain,
% 58.19/58.39      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 58.19/58.39      inference('cnf', [status(esa)], [t2_tsep_1])).
% 58.19/58.39  thf(t1_tsep_1, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_pre_topc @ A ) =>
% 58.19/58.39       ( ![B:$i]:
% 58.19/58.39         ( ( m1_pre_topc @ B @ A ) =>
% 58.19/58.39           ( m1_subset_1 @
% 58.19/58.39             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 58.19/58.39  thf('82', plain,
% 58.19/58.39      (![X20 : $i, X21 : $i]:
% 58.19/58.39         (~ (m1_pre_topc @ X20 @ X21)
% 58.19/58.39          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 58.19/58.39             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 58.19/58.39          | ~ (l1_pre_topc @ X21))),
% 58.19/58.39      inference('cnf', [status(esa)], [t1_tsep_1])).
% 58.19/58.39  thf('83', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         (~ (l1_pre_topc @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 58.19/58.39             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 58.19/58.39      inference('sup-', [status(thm)], ['81', '82'])).
% 58.19/58.39  thf('84', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 58.19/58.39           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 58.19/58.39          | ~ (l1_pre_topc @ X0))),
% 58.19/58.39      inference('simplify', [status(thm)], ['83'])).
% 58.19/58.39  thf('85', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 58.19/58.39           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 58.19/58.39          | ~ (l1_struct_0 @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0))),
% 58.19/58.39      inference('sup+', [status(thm)], ['80', '84'])).
% 58.19/58.39  thf('86', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 58.19/58.39      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 58.19/58.39  thf('87', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         (~ (l1_pre_topc @ X0)
% 58.19/58.39          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 58.19/58.39             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 58.19/58.39      inference('clc', [status(thm)], ['85', '86'])).
% 58.19/58.39  thf('88', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['53', '54'])).
% 58.19/58.39  thf(t16_tsep_1, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 58.19/58.39       ( ![B:$i]:
% 58.19/58.39         ( ( m1_pre_topc @ B @ A ) =>
% 58.19/58.39           ( ![C:$i]:
% 58.19/58.39             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 58.19/58.39               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 58.19/58.39                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 58.19/58.39                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 58.19/58.39  thf('89', plain,
% 58.19/58.39      (![X17 : $i, X18 : $i, X19 : $i]:
% 58.19/58.39         (~ (m1_pre_topc @ X17 @ X18)
% 58.19/58.39          | ((X19) != (u1_struct_0 @ X17))
% 58.19/58.39          | ~ (v3_pre_topc @ X19 @ X18)
% 58.19/58.39          | (v1_tsep_1 @ X17 @ X18)
% 58.19/58.39          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 58.19/58.39          | ~ (l1_pre_topc @ X18)
% 58.19/58.39          | ~ (v2_pre_topc @ X18))),
% 58.19/58.39      inference('cnf', [status(esa)], [t16_tsep_1])).
% 58.19/58.39  thf('90', plain,
% 58.19/58.39      (![X17 : $i, X18 : $i]:
% 58.19/58.39         (~ (v2_pre_topc @ X18)
% 58.19/58.39          | ~ (l1_pre_topc @ X18)
% 58.19/58.39          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 58.19/58.39               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 58.19/58.39          | (v1_tsep_1 @ X17 @ X18)
% 58.19/58.39          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 58.19/58.39          | ~ (m1_pre_topc @ X17 @ X18))),
% 58.19/58.39      inference('simplify', [status(thm)], ['89'])).
% 58.19/58.39  thf('91', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 58.19/58.39             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 58.19/58.39          | ~ (m1_pre_topc @ X0 @ sk_D)
% 58.19/58.39          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 58.19/58.39          | (v1_tsep_1 @ X0 @ sk_D)
% 58.19/58.39          | ~ (l1_pre_topc @ sk_D)
% 58.19/58.39          | ~ (v2_pre_topc @ sk_D))),
% 58.19/58.39      inference('sup-', [status(thm)], ['88', '90'])).
% 58.19/58.39  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['16', '17'])).
% 58.19/58.39  thf('93', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf(cc1_pre_topc, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 58.19/58.39       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 58.19/58.39  thf('94', plain,
% 58.19/58.39      (![X1 : $i, X2 : $i]:
% 58.19/58.39         (~ (m1_pre_topc @ X1 @ X2)
% 58.19/58.39          | (v2_pre_topc @ X1)
% 58.19/58.39          | ~ (l1_pre_topc @ X2)
% 58.19/58.39          | ~ (v2_pre_topc @ X2))),
% 58.19/58.39      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 58.19/58.39  thf('95', plain,
% 58.19/58.39      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 58.19/58.39      inference('sup-', [status(thm)], ['93', '94'])).
% 58.19/58.39  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('98', plain, ((v2_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['95', '96', '97'])).
% 58.19/58.39  thf('99', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 58.19/58.39             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 58.19/58.39          | ~ (m1_pre_topc @ X0 @ sk_D)
% 58.19/58.39          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 58.19/58.39          | (v1_tsep_1 @ X0 @ sk_D))),
% 58.19/58.39      inference('demod', [status(thm)], ['91', '92', '98'])).
% 58.19/58.39  thf('100', plain,
% 58.19/58.39      ((~ (l1_pre_topc @ sk_C)
% 58.19/58.39        | (v1_tsep_1 @ sk_C @ sk_D)
% 58.19/58.39        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 58.19/58.39        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 58.19/58.39      inference('sup-', [status(thm)], ['87', '99'])).
% 58.19/58.39  thf('101', plain, ((l1_pre_topc @ sk_C)),
% 58.19/58.39      inference('demod', [status(thm)], ['42', '43'])).
% 58.19/58.39  thf('102', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['35', '58'])).
% 58.19/58.39  thf('103', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['56', '57'])).
% 58.19/58.39  thf(fc10_tops_1, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 58.19/58.39       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 58.19/58.39  thf('104', plain,
% 58.19/58.39      (![X14 : $i]:
% 58.19/58.39         ((v3_pre_topc @ (k2_struct_0 @ X14) @ X14)
% 58.19/58.39          | ~ (l1_pre_topc @ X14)
% 58.19/58.39          | ~ (v2_pre_topc @ X14))),
% 58.19/58.39      inference('cnf', [status(esa)], [fc10_tops_1])).
% 58.19/58.39  thf('105', plain,
% 58.19/58.39      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 58.19/58.39        | ~ (v2_pre_topc @ sk_D)
% 58.19/58.39        | ~ (l1_pre_topc @ sk_D))),
% 58.19/58.39      inference('sup+', [status(thm)], ['103', '104'])).
% 58.19/58.39  thf('106', plain, ((v2_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['95', '96', '97'])).
% 58.19/58.39  thf('107', plain, ((l1_pre_topc @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['16', '17'])).
% 58.19/58.39  thf('108', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['105', '106', '107'])).
% 58.19/58.39  thf('109', plain,
% 58.19/58.39      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('110', plain,
% 58.19/58.39      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 58.19/58.39      inference('cnf', [status(esa)], [t2_tsep_1])).
% 58.19/58.39  thf(t65_pre_topc, axiom,
% 58.19/58.39    (![A:$i]:
% 58.19/58.39     ( ( l1_pre_topc @ A ) =>
% 58.19/58.39       ( ![B:$i]:
% 58.19/58.39         ( ( l1_pre_topc @ B ) =>
% 58.19/58.39           ( ( m1_pre_topc @ A @ B ) <=>
% 58.19/58.39             ( m1_pre_topc @
% 58.19/58.39               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 58.19/58.39  thf('111', plain,
% 58.19/58.39      (![X12 : $i, X13 : $i]:
% 58.19/58.39         (~ (l1_pre_topc @ X12)
% 58.19/58.39          | ~ (m1_pre_topc @ X13 @ X12)
% 58.19/58.39          | (m1_pre_topc @ X13 @ 
% 58.19/58.39             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 58.19/58.39          | ~ (l1_pre_topc @ X13))),
% 58.19/58.39      inference('cnf', [status(esa)], [t65_pre_topc])).
% 58.19/58.39  thf('112', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         (~ (l1_pre_topc @ X0)
% 58.19/58.39          | ~ (l1_pre_topc @ X0)
% 58.19/58.39          | (m1_pre_topc @ X0 @ 
% 58.19/58.39             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 58.19/58.39          | ~ (l1_pre_topc @ X0))),
% 58.19/58.39      inference('sup-', [status(thm)], ['110', '111'])).
% 58.19/58.39  thf('113', plain,
% 58.19/58.39      (![X0 : $i]:
% 58.19/58.39         ((m1_pre_topc @ X0 @ 
% 58.19/58.39           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 58.19/58.39          | ~ (l1_pre_topc @ X0))),
% 58.19/58.39      inference('simplify', [status(thm)], ['112'])).
% 58.19/58.39  thf('114', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 58.19/58.39      inference('sup+', [status(thm)], ['109', '113'])).
% 58.19/58.39  thf('115', plain, ((l1_pre_topc @ sk_C)),
% 58.19/58.39      inference('demod', [status(thm)], ['42', '43'])).
% 58.19/58.39  thf('116', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['114', '115'])).
% 58.19/58.39  thf('117', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['100', '101', '102', '108', '116'])).
% 58.19/58.39  thf('118', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 58.19/58.39      inference('demod', [status(thm)], ['114', '115'])).
% 58.19/58.39  thf('119', plain,
% 58.19/58.39      (![X3 : $i]:
% 58.19/58.39         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 58.19/58.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 58.19/58.39  thf('120', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('121', plain, (((sk_F) = (sk_G))),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('122', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['120', '121'])).
% 58.19/58.39  thf('123', plain,
% 58.19/58.39      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 58.19/58.39      inference('sup+', [status(thm)], ['119', '122'])).
% 58.19/58.39  thf('124', plain, ((l1_struct_0 @ sk_C)),
% 58.19/58.39      inference('sup-', [status(thm)], ['44', '45'])).
% 58.19/58.39  thf('125', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['123', '124'])).
% 58.19/58.39  thf('126', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['35', '58'])).
% 58.19/58.39  thf('127', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 58.19/58.39      inference('demod', [status(thm)], ['123', '124'])).
% 58.19/58.39  thf('128', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('131', plain,
% 58.19/58.39      (((v2_struct_0 @ sk_B)
% 58.19/58.39        | (v2_struct_0 @ sk_D)
% 58.19/58.39        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 58.19/58.39        | (v2_struct_0 @ sk_C)
% 58.19/58.39        | (v2_struct_0 @ sk_A))),
% 58.19/58.39      inference('demod', [status(thm)],
% 58.19/58.39                ['78', '79', '117', '118', '125', '126', '127', '128', '129', 
% 58.19/58.39                 '130'])).
% 58.19/58.39  thf('132', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('133', plain,
% 58.19/58.39      (((v2_struct_0 @ sk_A)
% 58.19/58.39        | (v2_struct_0 @ sk_C)
% 58.19/58.39        | (v2_struct_0 @ sk_D)
% 58.19/58.39        | (v2_struct_0 @ sk_B))),
% 58.19/58.39      inference('sup-', [status(thm)], ['131', '132'])).
% 58.19/58.39  thf('134', plain, (~ (v2_struct_0 @ sk_D)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('135', plain,
% 58.19/58.39      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 58.19/58.39      inference('sup-', [status(thm)], ['133', '134'])).
% 58.19/58.39  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('137', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 58.19/58.39      inference('clc', [status(thm)], ['135', '136'])).
% 58.19/58.39  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 58.19/58.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.19/58.39  thf('139', plain, ((v2_struct_0 @ sk_C)),
% 58.19/58.39      inference('clc', [status(thm)], ['137', '138'])).
% 58.19/58.39  thf('140', plain, ($false), inference('demod', [status(thm)], ['0', '139'])).
% 58.19/58.39  
% 58.19/58.39  % SZS output end Refutation
% 58.19/58.39  
% 58.19/58.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
