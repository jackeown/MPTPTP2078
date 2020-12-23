%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s6VLDLBYwr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:27 EST 2020

% Result     : Theorem 12.00s
% Output     : Refutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :  394 (5253 expanded)
%              Number of leaves         :   68 (1550 expanded)
%              Depth                    :   38
%              Number of atoms          : 3982 (153503 expanded)
%              Number of equality atoms :  115 (4426 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X34 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( ( g1_pre_topc @ X37 @ X38 )
       != ( g1_pre_topc @ X35 @ X36 ) )
      | ( X37 = X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( l1_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['8','9','14','15'])).

thf('17',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('18',plain,(
    ! [X60: $i] :
      ( ( m1_pre_topc @ X60 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( m1_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( l1_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( m1_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_pre_topc @ X53 @ X54 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X53 ) @ ( u1_pre_topc @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_pre_topc @ X53 @ X54 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X53 ) @ ( u1_pre_topc @ X53 ) ) @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( l1_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','44','45'])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('48',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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

thf('54',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_pre_topc @ X49 @ X50 )
      | ~ ( m1_pre_topc @ X49 @ X51 )
      | ( ( k3_tmap_1 @ X50 @ X48 @ X51 @ X49 @ X52 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X48 ) @ X52 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( v1_funct_2 @ X52 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X48 ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_pre_topc @ X51 @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['51','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['22','27'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_pre_topc @ X45 @ X46 )
      | ( ( k2_tmap_1 @ X46 @ X44 @ X47 @ X45 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) @ X47 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('74',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('79',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['71','77','78','79','80','81','82'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X60: $i] :
      ( ( m1_pre_topc @ X60 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_pre_topc @ X45 @ X46 )
      | ( ( k2_tmap_1 @ X46 @ X44 @ X47 @ X45 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) @ X47 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('99',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('104',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('107',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['96','102','103','104','107','108','109'])).

thf('111',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('113',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['90','118'])).

thf('120',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['22','27'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['67','119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(demod,[status(thm)],['50','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(t67_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( v2_struct_0 @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( v1_tsep_1 @ X62 @ X61 )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X62 ) )
      | ~ ( r1_tmap_1 @ X62 @ X64 @ ( k2_tmap_1 @ X61 @ X64 @ X65 @ X62 ) @ X63 )
      | ( r1_tmap_1 @ X61 @ X64 @ X65 @ X66 )
      | ( X66 != X63 )
      | ~ ( m1_subset_1 @ X66 @ ( u1_struct_0 @ X61 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( v2_pre_topc @ X64 )
      | ( v2_struct_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('129',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( v2_struct_0 @ X64 )
      | ~ ( v2_pre_topc @ X64 )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X61 ) )
      | ( r1_tmap_1 @ X61 @ X64 @ X65 @ X63 )
      | ~ ( r1_tmap_1 @ X62 @ X64 @ ( k2_tmap_1 @ X61 @ X64 @ X65 @ X62 ) @ X63 )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X62 ) )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ~ ( v1_tsep_1 @ X62 @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ( v2_struct_0 @ X61 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('132',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('133',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('134',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['126','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('143',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['22','27'])).

thf('144',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) )
      | ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('151',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('154',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X34 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('155',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( ( g1_pre_topc @ X37 @ X38 )
       != ( g1_pre_topc @ X35 @ X36 ) )
      | ( X38 = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( u1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('162',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ( ( u1_pre_topc @ sk_D )
      = ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','44','45'])).

thf('165',plain,
    ( ( u1_pre_topc @ sk_D )
    = ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('166',plain,(
    ! [X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ( r2_hidden @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('167',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('169',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('170',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('172',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['170','171'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('173',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('175',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('176',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['172','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('180',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

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

thf('182',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( X57
       != ( u1_struct_0 @ X55 ) )
      | ~ ( v3_pre_topc @ X57 @ X56 )
      | ( v1_tsep_1 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('183',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v2_pre_topc @ X56 )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v1_tsep_1 @ X55 @ X56 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X55 ) @ X56 )
      | ~ ( m1_pre_topc @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','183'])).

thf('185',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v1_tsep_1 @ sk_C_1 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['180','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('187',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('188',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['149','150'])).

thf('189',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['138','141','142','151','189'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('197',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( v2_struct_0 @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( v1_tsep_1 @ X62 @ X61 )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X62 ) )
      | ~ ( r1_tmap_1 @ X61 @ X64 @ X65 @ X66 )
      | ( r1_tmap_1 @ X62 @ X64 @ ( k2_tmap_1 @ X61 @ X64 @ X65 @ X62 ) @ X63 )
      | ( X66 != X63 )
      | ~ ( m1_subset_1 @ X66 @ ( u1_struct_0 @ X61 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( v2_pre_topc @ X64 )
      | ( v2_struct_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('198',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( v2_struct_0 @ X64 )
      | ~ ( v2_pre_topc @ X64 )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X61 ) )
      | ( r1_tmap_1 @ X62 @ X64 @ ( k2_tmap_1 @ X61 @ X64 @ X65 @ X62 ) @ X63 )
      | ~ ( r1_tmap_1 @ X61 @ X64 @ X65 @ X63 )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X62 ) )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ~ ( v1_tsep_1 @ X62 @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ( v2_struct_0 @ X61 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['196','198'])).

thf('200',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('201',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('202',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('203',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203','204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['195','206'])).

thf('208',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D ) @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('212',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X60: $i] :
      ( ( m1_pre_topc @ X60 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('214',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_pre_topc @ X53 @ X54 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X53 ) @ ( u1_pre_topc @ X53 ) ) @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('217',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_pre_topc @ X58 @ X59 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X58 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v2_pre_topc @ X56 )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v1_tsep_1 @ X55 @ X56 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X55 ) @ X56 )
      | ~ ( m1_pre_topc @ X55 @ X56 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X0 )
      | ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['212','222'])).

thf('224',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('225',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['178','179'])).

thf('226',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('227',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X60: $i] :
      ( ( m1_pre_topc @ X60 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('230',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) )
      | ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['228','232'])).

thf('234',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('235',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('237',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('238',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('240',plain,(
    v1_tsep_1 @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['223','224','225','226','227','237','238','239'])).

thf('241',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['96','102','103','104','107','108','109'])).

thf('244',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('246',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('249',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D )
      = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['244','245','246','247','248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D )
      = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('256',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['210','211','240','241','256'])).

thf('258',plain,(
    ! [X60: $i] :
      ( ( m1_pre_topc @ X60 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('260',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('262',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('269',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['267','268'])).

thf('270',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('271',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('273',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('274',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( v2_struct_0 @ X64 )
      | ~ ( v2_pre_topc @ X64 )
      | ~ ( l1_pre_topc @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X64 ) ) ) )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X61 ) )
      | ( r1_tmap_1 @ X61 @ X64 @ X65 @ X63 )
      | ~ ( r1_tmap_1 @ X62 @ X64 @ ( k2_tmap_1 @ X61 @ X64 @ X65 @ X62 ) @ X63 )
      | ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X62 ) )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ~ ( v1_tsep_1 @ X62 @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ( v2_struct_0 @ X61 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('277',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('278',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('279',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('280',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['275','276','277','278','279'])).

thf('281',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['272','280'])).

thf('282',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['281','282','283','284','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_D @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['271','286'])).

thf('288',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','183'])).

thf('290',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('292',plain,(
    ! [X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ( r2_hidden @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('293',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('294',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['291','295'])).

thf('297',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('298',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('299',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('301',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('302',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('303',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( m1_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('304',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('306',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('308',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['304','305','306','307'])).

thf('309',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['290','299','300','301','308'])).

thf('310',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['304','305','306','307'])).

thf('311',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['287','309','310','311'])).

thf('313',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['257','313'])).

thf('315',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('316',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['314','315'])).

thf('317',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('322',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['321','322'])).

thf('324',plain,(
    $false ),
    inference(demod,[status(thm)],['0','323'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s6VLDLBYwr
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.00/12.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.00/12.25  % Solved by: fo/fo7.sh
% 12.00/12.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.00/12.25  % done 11594 iterations in 11.786s
% 12.00/12.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.00/12.25  % SZS output start Refutation
% 12.00/12.25  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 12.00/12.25  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 12.00/12.25  thf(sk_E_type, type, sk_E: $i).
% 12.00/12.25  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 12.00/12.25  thf(sk_A_type, type, sk_A: $i).
% 12.00/12.25  thf(sk_G_type, type, sk_G: $i).
% 12.00/12.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.00/12.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.00/12.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.00/12.25  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 12.00/12.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.00/12.25  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 12.00/12.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.00/12.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.00/12.25  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 12.00/12.25  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 12.00/12.25  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 12.00/12.25  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 12.00/12.25  thf(sk_B_2_type, type, sk_B_2: $i).
% 12.00/12.25  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 12.00/12.25  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 12.00/12.25  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 12.00/12.25  thf(sk_D_type, type, sk_D: $i).
% 12.00/12.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 12.00/12.25  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 12.00/12.25  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 12.00/12.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 12.00/12.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.00/12.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.00/12.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.00/12.25  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 12.00/12.25  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 12.00/12.25  thf(sk_F_type, type, sk_F: $i).
% 12.00/12.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.00/12.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 12.00/12.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.00/12.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 12.00/12.25  thf(t88_tmap_1, conjecture,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.00/12.25       ( ![B:$i]:
% 12.00/12.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 12.00/12.25             ( l1_pre_topc @ B ) ) =>
% 12.00/12.25           ( ![C:$i]:
% 12.00/12.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 12.00/12.25               ( ![D:$i]:
% 12.00/12.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 12.00/12.25                   ( ![E:$i]:
% 12.00/12.25                     ( ( ( v1_funct_1 @ E ) & 
% 12.00/12.25                         ( v1_funct_2 @
% 12.00/12.25                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 12.00/12.25                         ( m1_subset_1 @
% 12.00/12.25                           E @ 
% 12.00/12.25                           ( k1_zfmisc_1 @
% 12.00/12.25                             ( k2_zfmisc_1 @
% 12.00/12.25                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 12.00/12.25                       ( ( ( g1_pre_topc @
% 12.00/12.25                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 12.00/12.25                           ( D ) ) =>
% 12.00/12.25                         ( ![F:$i]:
% 12.00/12.25                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 12.00/12.25                             ( ![G:$i]:
% 12.00/12.25                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 12.00/12.25                                 ( ( ( ( F ) = ( G ) ) & 
% 12.00/12.25                                     ( r1_tmap_1 @
% 12.00/12.25                                       C @ B @ 
% 12.00/12.25                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 12.00/12.25                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.00/12.25  thf(zf_stmt_0, negated_conjecture,
% 12.00/12.25    (~( ![A:$i]:
% 12.00/12.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 12.00/12.25            ( l1_pre_topc @ A ) ) =>
% 12.00/12.25          ( ![B:$i]:
% 12.00/12.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 12.00/12.25                ( l1_pre_topc @ B ) ) =>
% 12.00/12.25              ( ![C:$i]:
% 12.00/12.25                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 12.00/12.25                  ( ![D:$i]:
% 12.00/12.25                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 12.00/12.25                      ( ![E:$i]:
% 12.00/12.25                        ( ( ( v1_funct_1 @ E ) & 
% 12.00/12.25                            ( v1_funct_2 @
% 12.00/12.25                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 12.00/12.25                            ( m1_subset_1 @
% 12.00/12.25                              E @ 
% 12.00/12.25                              ( k1_zfmisc_1 @
% 12.00/12.25                                ( k2_zfmisc_1 @
% 12.00/12.25                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 12.00/12.25                          ( ( ( g1_pre_topc @
% 12.00/12.25                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 12.00/12.25                              ( D ) ) =>
% 12.00/12.25                            ( ![F:$i]:
% 12.00/12.25                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 12.00/12.25                                ( ![G:$i]:
% 12.00/12.25                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 12.00/12.25                                    ( ( ( ( F ) = ( G ) ) & 
% 12.00/12.25                                        ( r1_tmap_1 @
% 12.00/12.25                                          C @ B @ 
% 12.00/12.25                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 12.00/12.25                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 12.00/12.25    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 12.00/12.25  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('1', plain,
% 12.00/12.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.25         = (sk_D))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf(abstractness_v1_pre_topc, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( l1_pre_topc @ A ) =>
% 12.00/12.25       ( ( v1_pre_topc @ A ) =>
% 12.00/12.25         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 12.00/12.25  thf('2', plain,
% 12.00/12.25      (![X2 : $i]:
% 12.00/12.25         (~ (v1_pre_topc @ X2)
% 12.00/12.25          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 12.00/12.25          | ~ (l1_pre_topc @ X2))),
% 12.00/12.25      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 12.00/12.25  thf(dt_u1_pre_topc, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( l1_pre_topc @ A ) =>
% 12.00/12.25       ( m1_subset_1 @
% 12.00/12.25         ( u1_pre_topc @ A ) @ 
% 12.00/12.25         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 12.00/12.25  thf('3', plain,
% 12.00/12.25      (![X34 : $i]:
% 12.00/12.25         ((m1_subset_1 @ (u1_pre_topc @ X34) @ 
% 12.00/12.25           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 12.00/12.25          | ~ (l1_pre_topc @ X34))),
% 12.00/12.25      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 12.00/12.25  thf(free_g1_pre_topc, axiom,
% 12.00/12.25    (![A:$i,B:$i]:
% 12.00/12.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.00/12.25       ( ![C:$i,D:$i]:
% 12.00/12.25         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 12.00/12.25           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 12.00/12.25  thf('4', plain,
% 12.00/12.25      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 12.00/12.25         (((g1_pre_topc @ X37 @ X38) != (g1_pre_topc @ X35 @ X36))
% 12.00/12.25          | ((X37) = (X35))
% 12.00/12.25          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X37))))),
% 12.00/12.25      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 12.00/12.25  thf('5', plain,
% 12.00/12.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.00/12.25         (~ (l1_pre_topc @ X0)
% 12.00/12.25          | ((u1_struct_0 @ X0) = (X1))
% 12.00/12.25          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 12.00/12.25              != (g1_pre_topc @ X1 @ X2)))),
% 12.00/12.25      inference('sup-', [status(thm)], ['3', '4'])).
% 12.00/12.25  thf('6', plain,
% 12.00/12.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.00/12.25         (((X0) != (g1_pre_topc @ X2 @ X1))
% 12.00/12.25          | ~ (l1_pre_topc @ X0)
% 12.00/12.25          | ~ (v1_pre_topc @ X0)
% 12.00/12.25          | ((u1_struct_0 @ X0) = (X2))
% 12.00/12.25          | ~ (l1_pre_topc @ X0))),
% 12.00/12.25      inference('sup-', [status(thm)], ['2', '5'])).
% 12.00/12.25  thf('7', plain,
% 12.00/12.25      (![X1 : $i, X2 : $i]:
% 12.00/12.25         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 12.00/12.25          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 12.00/12.25          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 12.00/12.25      inference('simplify', [status(thm)], ['6'])).
% 12.00/12.25  thf('8', plain,
% 12.00/12.25      ((~ (v1_pre_topc @ sk_D)
% 12.00/12.25        | ~ (l1_pre_topc @ 
% 12.00/12.25             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 12.00/12.25        | ((u1_struct_0 @ 
% 12.00/12.25            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 12.00/12.25            = (u1_struct_0 @ sk_C_1)))),
% 12.00/12.25      inference('sup-', [status(thm)], ['1', '7'])).
% 12.00/12.25  thf('9', plain,
% 12.00/12.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.25         = (sk_D))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf(dt_m1_pre_topc, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( l1_pre_topc @ A ) =>
% 12.00/12.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 12.00/12.25  thf('11', plain,
% 12.00/12.25      (![X32 : $i, X33 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X32 @ X33)
% 12.00/12.25          | (l1_pre_topc @ X32)
% 12.00/12.25          | ~ (l1_pre_topc @ X33))),
% 12.00/12.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 12.00/12.25  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 12.00/12.25      inference('sup-', [status(thm)], ['10', '11'])).
% 12.00/12.25  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.25  thf('15', plain,
% 12.00/12.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.25         = (sk_D))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('16', plain,
% 12.00/12.25      ((~ (v1_pre_topc @ sk_D)
% 12.00/12.25        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1)))),
% 12.00/12.25      inference('demod', [status(thm)], ['8', '9', '14', '15'])).
% 12.00/12.25  thf('17', plain,
% 12.00/12.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.25         = (sk_D))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf(t2_tsep_1, axiom,
% 12.00/12.25    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 12.00/12.25  thf('18', plain,
% 12.00/12.25      (![X60 : $i]: ((m1_pre_topc @ X60 @ X60) | ~ (l1_pre_topc @ X60))),
% 12.00/12.25      inference('cnf', [status(esa)], [t2_tsep_1])).
% 12.00/12.25  thf(t65_pre_topc, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( l1_pre_topc @ A ) =>
% 12.00/12.25       ( ![B:$i]:
% 12.00/12.25         ( ( l1_pre_topc @ B ) =>
% 12.00/12.25           ( ( m1_pre_topc @ A @ B ) <=>
% 12.00/12.25             ( m1_pre_topc @
% 12.00/12.25               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 12.00/12.25  thf('19', plain,
% 12.00/12.25      (![X42 : $i, X43 : $i]:
% 12.00/12.25         (~ (l1_pre_topc @ X42)
% 12.00/12.25          | ~ (m1_pre_topc @ X43 @ X42)
% 12.00/12.25          | (m1_pre_topc @ X43 @ 
% 12.00/12.25             (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)))
% 12.00/12.25          | ~ (l1_pre_topc @ X43))),
% 12.00/12.25      inference('cnf', [status(esa)], [t65_pre_topc])).
% 12.00/12.25  thf('20', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         (~ (l1_pre_topc @ X0)
% 12.00/12.25          | ~ (l1_pre_topc @ X0)
% 12.00/12.25          | (m1_pre_topc @ X0 @ 
% 12.00/12.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 12.00/12.25          | ~ (l1_pre_topc @ X0))),
% 12.00/12.25      inference('sup-', [status(thm)], ['18', '19'])).
% 12.00/12.25  thf('21', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((m1_pre_topc @ X0 @ 
% 12.00/12.25           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 12.00/12.25          | ~ (l1_pre_topc @ X0))),
% 12.00/12.25      inference('simplify', [status(thm)], ['20'])).
% 12.00/12.25  thf('22', plain,
% 12.00/12.25      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 12.00/12.25      inference('sup+', [status(thm)], ['17', '21'])).
% 12.00/12.25  thf('23', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('24', plain,
% 12.00/12.25      (![X32 : $i, X33 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X32 @ X33)
% 12.00/12.25          | (l1_pre_topc @ X32)
% 12.00/12.25          | ~ (l1_pre_topc @ X33))),
% 12.00/12.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 12.00/12.25  thf('25', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 12.00/12.25      inference('sup-', [status(thm)], ['23', '24'])).
% 12.00/12.25  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.25  thf('28', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['22', '27'])).
% 12.00/12.25  thf('29', plain,
% 12.00/12.25      (![X42 : $i, X43 : $i]:
% 12.00/12.25         (~ (l1_pre_topc @ X42)
% 12.00/12.25          | ~ (m1_pre_topc @ X43 @ X42)
% 12.00/12.25          | (m1_pre_topc @ X43 @ 
% 12.00/12.25             (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)))
% 12.00/12.25          | ~ (l1_pre_topc @ X43))),
% 12.00/12.25      inference('cnf', [status(esa)], [t65_pre_topc])).
% 12.00/12.25  thf('30', plain,
% 12.00/12.25      ((~ (l1_pre_topc @ sk_C_1)
% 12.00/12.25        | (m1_pre_topc @ sk_C_1 @ 
% 12.00/12.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 12.00/12.25        | ~ (l1_pre_topc @ sk_D))),
% 12.00/12.25      inference('sup-', [status(thm)], ['28', '29'])).
% 12.00/12.25  thf('31', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.25  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.25  thf('33', plain,
% 12.00/12.25      ((m1_pre_topc @ sk_C_1 @ 
% 12.00/12.25        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 12.00/12.25      inference('demod', [status(thm)], ['30', '31', '32'])).
% 12.00/12.25  thf(t11_tmap_1, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( l1_pre_topc @ A ) =>
% 12.00/12.25       ( ![B:$i]:
% 12.00/12.25         ( ( m1_pre_topc @ B @ A ) =>
% 12.00/12.25           ( ( v1_pre_topc @
% 12.00/12.25               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 12.00/12.25             ( m1_pre_topc @
% 12.00/12.25               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 12.00/12.25  thf('34', plain,
% 12.00/12.25      (![X53 : $i, X54 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X53 @ X54)
% 12.00/12.25          | (v1_pre_topc @ 
% 12.00/12.25             (g1_pre_topc @ (u1_struct_0 @ X53) @ (u1_pre_topc @ X53)))
% 12.00/12.25          | ~ (l1_pre_topc @ X54))),
% 12.00/12.25      inference('cnf', [status(esa)], [t11_tmap_1])).
% 12.00/12.25  thf('35', plain,
% 12.00/12.25      ((~ (l1_pre_topc @ 
% 12.00/12.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 12.00/12.25        | (v1_pre_topc @ 
% 12.00/12.25           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))))),
% 12.00/12.25      inference('sup-', [status(thm)], ['33', '34'])).
% 12.00/12.25  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('37', plain,
% 12.00/12.25      (![X53 : $i, X54 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X53 @ X54)
% 12.00/12.25          | (m1_pre_topc @ 
% 12.00/12.25             (g1_pre_topc @ (u1_struct_0 @ X53) @ (u1_pre_topc @ X53)) @ X54)
% 12.00/12.25          | ~ (l1_pre_topc @ X54))),
% 12.00/12.25      inference('cnf', [status(esa)], [t11_tmap_1])).
% 12.00/12.25  thf('38', plain,
% 12.00/12.25      ((~ (l1_pre_topc @ sk_A)
% 12.00/12.25        | (m1_pre_topc @ 
% 12.00/12.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_A))),
% 12.00/12.25      inference('sup-', [status(thm)], ['36', '37'])).
% 12.00/12.25  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('40', plain,
% 12.00/12.25      ((m1_pre_topc @ 
% 12.00/12.25        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_A)),
% 12.00/12.25      inference('demod', [status(thm)], ['38', '39'])).
% 12.00/12.25  thf('41', plain,
% 12.00/12.25      (![X32 : $i, X33 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X32 @ X33)
% 12.00/12.25          | (l1_pre_topc @ X32)
% 12.00/12.25          | ~ (l1_pre_topc @ X33))),
% 12.00/12.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 12.00/12.25  thf('42', plain,
% 12.00/12.25      ((~ (l1_pre_topc @ sk_A)
% 12.00/12.25        | (l1_pre_topc @ 
% 12.00/12.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 12.00/12.25      inference('sup-', [status(thm)], ['40', '41'])).
% 12.00/12.25  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('44', plain,
% 12.00/12.25      ((l1_pre_topc @ 
% 12.00/12.25        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 12.00/12.25      inference('demod', [status(thm)], ['42', '43'])).
% 12.00/12.25  thf('45', plain,
% 12.00/12.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.25         = (sk_D))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('46', plain, ((v1_pre_topc @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['35', '44', '45'])).
% 12.00/12.25  thf('47', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.25  thf('48', plain,
% 12.00/12.25      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 12.00/12.25        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('49', plain, (((sk_F) = (sk_G))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('50', plain,
% 12.00/12.25      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 12.00/12.25        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 12.00/12.25      inference('demod', [status(thm)], ['48', '49'])).
% 12.00/12.25  thf('51', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('52', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('53', plain,
% 12.00/12.25      ((m1_subset_1 @ sk_E @ 
% 12.00/12.25        (k1_zfmisc_1 @ 
% 12.00/12.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf(d5_tmap_1, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.00/12.25       ( ![B:$i]:
% 12.00/12.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 12.00/12.25             ( l1_pre_topc @ B ) ) =>
% 12.00/12.25           ( ![C:$i]:
% 12.00/12.25             ( ( m1_pre_topc @ C @ A ) =>
% 12.00/12.25               ( ![D:$i]:
% 12.00/12.25                 ( ( m1_pre_topc @ D @ A ) =>
% 12.00/12.25                   ( ![E:$i]:
% 12.00/12.25                     ( ( ( v1_funct_1 @ E ) & 
% 12.00/12.25                         ( v1_funct_2 @
% 12.00/12.25                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 12.00/12.25                         ( m1_subset_1 @
% 12.00/12.25                           E @ 
% 12.00/12.25                           ( k1_zfmisc_1 @
% 12.00/12.25                             ( k2_zfmisc_1 @
% 12.00/12.25                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 12.00/12.25                       ( ( m1_pre_topc @ D @ C ) =>
% 12.00/12.25                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 12.00/12.25                           ( k2_partfun1 @
% 12.00/12.25                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 12.00/12.25                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.00/12.25  thf('54', plain,
% 12.00/12.25      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X48)
% 12.00/12.25          | ~ (v2_pre_topc @ X48)
% 12.00/12.25          | ~ (l1_pre_topc @ X48)
% 12.00/12.25          | ~ (m1_pre_topc @ X49 @ X50)
% 12.00/12.25          | ~ (m1_pre_topc @ X49 @ X51)
% 12.00/12.25          | ((k3_tmap_1 @ X50 @ X48 @ X51 @ X49 @ X52)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X48) @ 
% 12.00/12.25                 X52 @ (u1_struct_0 @ X49)))
% 12.00/12.25          | ~ (m1_subset_1 @ X52 @ 
% 12.00/12.25               (k1_zfmisc_1 @ 
% 12.00/12.25                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X48))))
% 12.00/12.25          | ~ (v1_funct_2 @ X52 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X48))
% 12.00/12.25          | ~ (v1_funct_1 @ X52)
% 12.00/12.25          | ~ (m1_pre_topc @ X51 @ X50)
% 12.00/12.25          | ~ (l1_pre_topc @ X50)
% 12.00/12.25          | ~ (v2_pre_topc @ X50)
% 12.00/12.25          | (v2_struct_0 @ X50))),
% 12.00/12.25      inference('cnf', [status(esa)], [d5_tmap_1])).
% 12.00/12.25  thf('55', plain,
% 12.00/12.25      (![X0 : $i, X1 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X0)
% 12.00/12.25          | ~ (v2_pre_topc @ X0)
% 12.00/12.25          | ~ (l1_pre_topc @ X0)
% 12.00/12.25          | ~ (m1_pre_topc @ sk_D @ X0)
% 12.00/12.25          | ~ (v1_funct_1 @ sk_E)
% 12.00/12.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 12.00/12.25               (u1_struct_0 @ sk_B_2))
% 12.00/12.25          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25                 sk_E @ (u1_struct_0 @ X1)))
% 12.00/12.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 12.00/12.25          | ~ (m1_pre_topc @ X1 @ X0)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_B_2)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_B_2)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('sup-', [status(thm)], ['53', '54'])).
% 12.00/12.25  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('57', plain,
% 12.00/12.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('58', plain, ((l1_pre_topc @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('59', plain, ((v2_pre_topc @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('60', plain,
% 12.00/12.25      (![X0 : $i, X1 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X0)
% 12.00/12.25          | ~ (v2_pre_topc @ X0)
% 12.00/12.25          | ~ (l1_pre_topc @ X0)
% 12.00/12.25          | ~ (m1_pre_topc @ sk_D @ X0)
% 12.00/12.25          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25                 sk_E @ (u1_struct_0 @ X1)))
% 12.00/12.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 12.00/12.25          | ~ (m1_pre_topc @ X1 @ X0)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 12.00/12.25  thf('61', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.25  thf('62', plain,
% 12.00/12.25      (![X0 : $i, X1 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X0)
% 12.00/12.25          | ~ (v2_pre_topc @ X0)
% 12.00/12.25          | ~ (l1_pre_topc @ X0)
% 12.00/12.25          | ~ (m1_pre_topc @ sk_D @ X0)
% 12.00/12.25          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X1)))
% 12.00/12.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 12.00/12.25          | ~ (m1_pre_topc @ X1 @ X0)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)], ['60', '61'])).
% 12.00/12.25  thf('63', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_B_2)
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_A)
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.25          | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ X0 @ sk_E)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | ~ (l1_pre_topc @ sk_A)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_A)
% 12.00/12.25          | (v2_struct_0 @ sk_A))),
% 12.00/12.25      inference('sup-', [status(thm)], ['52', '62'])).
% 12.00/12.25  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('66', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_B_2)
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_A)
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.25          | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ X0 @ sk_E)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | (v2_struct_0 @ sk_A))),
% 12.00/12.25      inference('demod', [status(thm)], ['63', '64', '65'])).
% 12.00/12.25  thf('67', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_A)
% 12.00/12.25        | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 12.00/12.25            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25               sk_E @ (u1_struct_0 @ sk_C_1)))
% 12.00/12.25        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 12.00/12.25        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('sup-', [status(thm)], ['51', '66'])).
% 12.00/12.25  thf('68', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['22', '27'])).
% 12.00/12.25  thf('69', plain,
% 12.00/12.25      ((m1_subset_1 @ sk_E @ 
% 12.00/12.25        (k1_zfmisc_1 @ 
% 12.00/12.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf(d4_tmap_1, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.00/12.25       ( ![B:$i]:
% 12.00/12.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 12.00/12.25             ( l1_pre_topc @ B ) ) =>
% 12.00/12.25           ( ![C:$i]:
% 12.00/12.25             ( ( ( v1_funct_1 @ C ) & 
% 12.00/12.25                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 12.00/12.25                 ( m1_subset_1 @
% 12.00/12.25                   C @ 
% 12.00/12.25                   ( k1_zfmisc_1 @
% 12.00/12.25                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 12.00/12.25               ( ![D:$i]:
% 12.00/12.25                 ( ( m1_pre_topc @ D @ A ) =>
% 12.00/12.25                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 12.00/12.25                     ( k2_partfun1 @
% 12.00/12.25                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 12.00/12.25                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 12.00/12.25  thf('70', plain,
% 12.00/12.25      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X44)
% 12.00/12.25          | ~ (v2_pre_topc @ X44)
% 12.00/12.25          | ~ (l1_pre_topc @ X44)
% 12.00/12.25          | ~ (m1_pre_topc @ X45 @ X46)
% 12.00/12.25          | ((k2_tmap_1 @ X46 @ X44 @ X47 @ X45)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44) @ 
% 12.00/12.25                 X47 @ (u1_struct_0 @ X45)))
% 12.00/12.25          | ~ (m1_subset_1 @ X47 @ 
% 12.00/12.25               (k1_zfmisc_1 @ 
% 12.00/12.25                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))))
% 12.00/12.25          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))
% 12.00/12.25          | ~ (v1_funct_1 @ X47)
% 12.00/12.25          | ~ (l1_pre_topc @ X46)
% 12.00/12.25          | ~ (v2_pre_topc @ X46)
% 12.00/12.25          | (v2_struct_0 @ X46))),
% 12.00/12.25      inference('cnf', [status(esa)], [d4_tmap_1])).
% 12.00/12.25  thf('71', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_D)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_D)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_D)
% 12.00/12.25          | ~ (v1_funct_1 @ sk_E)
% 12.00/12.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 12.00/12.25               (u1_struct_0 @ sk_B_2))
% 12.00/12.25          | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25                 sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_B_2)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_B_2)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('sup-', [status(thm)], ['69', '70'])).
% 12.00/12.25  thf('72', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf(cc1_pre_topc, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.00/12.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 12.00/12.25  thf('73', plain,
% 12.00/12.25      (![X3 : $i, X4 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X3 @ X4)
% 12.00/12.25          | (v2_pre_topc @ X3)
% 12.00/12.25          | ~ (l1_pre_topc @ X4)
% 12.00/12.25          | ~ (v2_pre_topc @ X4))),
% 12.00/12.25      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 12.00/12.25  thf('74', plain,
% 12.00/12.25      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 12.00/12.25      inference('sup-', [status(thm)], ['72', '73'])).
% 12.00/12.25  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('77', plain, ((v2_pre_topc @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['74', '75', '76'])).
% 12.00/12.25  thf('78', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.25  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('80', plain,
% 12.00/12.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('81', plain, ((l1_pre_topc @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('82', plain, ((v2_pre_topc @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('83', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_D)
% 12.00/12.25          | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25                 sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)],
% 12.00/12.25                ['71', '77', '78', '79', '80', '81', '82'])).
% 12.00/12.25  thf('84', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.25  thf('85', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_D)
% 12.00/12.25          | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)], ['83', '84'])).
% 12.00/12.25  thf('86', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_B_2)
% 12.00/12.25        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25               sk_E @ (u1_struct_0 @ sk_C_1)))
% 12.00/12.25        | (v2_struct_0 @ sk_D))),
% 12.00/12.25      inference('sup-', [status(thm)], ['68', '85'])).
% 12.00/12.25  thf('87', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('88', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_D)
% 12.00/12.25        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 12.00/12.25      inference('clc', [status(thm)], ['86', '87'])).
% 12.00/12.25  thf('89', plain, (~ (v2_struct_0 @ sk_D)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('90', plain,
% 12.00/12.25      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 12.00/12.25      inference('clc', [status(thm)], ['88', '89'])).
% 12.00/12.25  thf('91', plain,
% 12.00/12.25      (![X60 : $i]: ((m1_pre_topc @ X60 @ X60) | ~ (l1_pre_topc @ X60))),
% 12.00/12.25      inference('cnf', [status(esa)], [t2_tsep_1])).
% 12.00/12.25  thf('92', plain,
% 12.00/12.25      ((m1_subset_1 @ sk_E @ 
% 12.00/12.25        (k1_zfmisc_1 @ 
% 12.00/12.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('93', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.25  thf('94', plain,
% 12.00/12.25      ((m1_subset_1 @ sk_E @ 
% 12.00/12.25        (k1_zfmisc_1 @ 
% 12.00/12.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.25      inference('demod', [status(thm)], ['92', '93'])).
% 12.00/12.25  thf('95', plain,
% 12.00/12.25      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X44)
% 12.00/12.25          | ~ (v2_pre_topc @ X44)
% 12.00/12.25          | ~ (l1_pre_topc @ X44)
% 12.00/12.25          | ~ (m1_pre_topc @ X45 @ X46)
% 12.00/12.25          | ((k2_tmap_1 @ X46 @ X44 @ X47 @ X45)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44) @ 
% 12.00/12.25                 X47 @ (u1_struct_0 @ X45)))
% 12.00/12.25          | ~ (m1_subset_1 @ X47 @ 
% 12.00/12.25               (k1_zfmisc_1 @ 
% 12.00/12.25                (k2_zfmisc_1 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))))
% 12.00/12.25          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X44))
% 12.00/12.25          | ~ (v1_funct_1 @ X47)
% 12.00/12.25          | ~ (l1_pre_topc @ X46)
% 12.00/12.25          | ~ (v2_pre_topc @ X46)
% 12.00/12.25          | (v2_struct_0 @ X46))),
% 12.00/12.25      inference('cnf', [status(esa)], [d4_tmap_1])).
% 12.00/12.25  thf('96', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_C_1)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_C_1)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_C_1)
% 12.00/12.25          | ~ (v1_funct_1 @ sk_E)
% 12.00/12.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25               (u1_struct_0 @ sk_B_2))
% 12.00/12.25          | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_B_2)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_B_2)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('sup-', [status(thm)], ['94', '95'])).
% 12.00/12.25  thf('97', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('98', plain,
% 12.00/12.25      (![X3 : $i, X4 : $i]:
% 12.00/12.25         (~ (m1_pre_topc @ X3 @ X4)
% 12.00/12.25          | (v2_pre_topc @ X3)
% 12.00/12.25          | ~ (l1_pre_topc @ X4)
% 12.00/12.25          | ~ (v2_pre_topc @ X4))),
% 12.00/12.25      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 12.00/12.25  thf('99', plain,
% 12.00/12.25      ((~ (v2_pre_topc @ sk_A)
% 12.00/12.25        | ~ (l1_pre_topc @ sk_A)
% 12.00/12.25        | (v2_pre_topc @ sk_C_1))),
% 12.00/12.25      inference('sup-', [status(thm)], ['97', '98'])).
% 12.00/12.25  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('102', plain, ((v2_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['99', '100', '101'])).
% 12.00/12.25  thf('103', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.25  thf('104', plain, ((v1_funct_1 @ sk_E)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('105', plain,
% 12.00/12.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('106', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.25  thf('107', plain,
% 12.00/12.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)], ['105', '106'])).
% 12.00/12.25  thf('108', plain, ((l1_pre_topc @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('109', plain, ((v2_pre_topc @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('110', plain,
% 12.00/12.25      (![X0 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_C_1)
% 12.00/12.25          | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0)
% 12.00/12.25              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)],
% 12.00/12.25                ['96', '102', '103', '104', '107', '108', '109'])).
% 12.00/12.25  thf('111', plain,
% 12.00/12.25      ((~ (l1_pre_topc @ sk_C_1)
% 12.00/12.25        | (v2_struct_0 @ sk_B_2)
% 12.00/12.25        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25               sk_E @ (u1_struct_0 @ sk_C_1)))
% 12.00/12.25        | (v2_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('sup-', [status(thm)], ['91', '110'])).
% 12.00/12.25  thf('112', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.25  thf('113', plain,
% 12.00/12.25      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 12.00/12.25      inference('clc', [status(thm)], ['88', '89'])).
% 12.00/12.25  thf('114', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_B_2)
% 12.00/12.25        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25            = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))
% 12.00/12.25        | (v2_struct_0 @ sk_C_1))),
% 12.00/12.25      inference('demod', [status(thm)], ['111', '112', '113'])).
% 12.00/12.25  thf('115', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('116', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_C_1)
% 12.00/12.25        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25            = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)))),
% 12.00/12.25      inference('clc', [status(thm)], ['114', '115'])).
% 12.00/12.25  thf('117', plain, (~ (v2_struct_0 @ sk_C_1)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('118', plain,
% 12.00/12.25      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))),
% 12.00/12.25      inference('clc', [status(thm)], ['116', '117'])).
% 12.00/12.25  thf('119', plain,
% 12.00/12.25      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.25         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.25            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 12.00/12.25      inference('demod', [status(thm)], ['90', '118'])).
% 12.00/12.25  thf('120', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 12.00/12.25      inference('demod', [status(thm)], ['22', '27'])).
% 12.00/12.25  thf('121', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_A)
% 12.00/12.25        | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 12.00/12.25            = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1))
% 12.00/12.25        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('demod', [status(thm)], ['67', '119', '120'])).
% 12.00/12.25  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('123', plain,
% 12.00/12.25      (((v2_struct_0 @ sk_B_2)
% 12.00/12.25        | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 12.00/12.25            = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)))),
% 12.00/12.25      inference('clc', [status(thm)], ['121', '122'])).
% 12.00/12.25  thf('124', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.25  thf('125', plain,
% 12.00/12.25      (((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 12.00/12.25         = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1))),
% 12.00/12.25      inference('clc', [status(thm)], ['123', '124'])).
% 12.00/12.25  thf('126', plain,
% 12.00/12.25      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 12.00/12.25        (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ sk_F)),
% 12.00/12.25      inference('demod', [status(thm)], ['50', '125'])).
% 12.00/12.25  thf('127', plain,
% 12.00/12.25      ((m1_subset_1 @ sk_E @ 
% 12.00/12.25        (k1_zfmisc_1 @ 
% 12.00/12.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.25      inference('demod', [status(thm)], ['92', '93'])).
% 12.00/12.25  thf(t67_tmap_1, axiom,
% 12.00/12.25    (![A:$i]:
% 12.00/12.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.00/12.25       ( ![B:$i]:
% 12.00/12.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 12.00/12.25             ( l1_pre_topc @ B ) ) =>
% 12.00/12.25           ( ![C:$i]:
% 12.00/12.25             ( ( ( v1_funct_1 @ C ) & 
% 12.00/12.25                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 12.00/12.25                 ( m1_subset_1 @
% 12.00/12.25                   C @ 
% 12.00/12.25                   ( k1_zfmisc_1 @
% 12.00/12.25                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 12.00/12.25               ( ![D:$i]:
% 12.00/12.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 12.00/12.25                     ( m1_pre_topc @ D @ B ) ) =>
% 12.00/12.25                   ( ![E:$i]:
% 12.00/12.25                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 12.00/12.25                       ( ![F:$i]:
% 12.00/12.25                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 12.00/12.25                           ( ( ( E ) = ( F ) ) =>
% 12.00/12.25                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 12.00/12.25                               ( r1_tmap_1 @
% 12.00/12.25                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.00/12.25  thf('128', plain,
% 12.00/12.25      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X61)
% 12.00/12.25          | ~ (v2_pre_topc @ X61)
% 12.00/12.25          | ~ (l1_pre_topc @ X61)
% 12.00/12.25          | (v2_struct_0 @ X62)
% 12.00/12.25          | ~ (v1_tsep_1 @ X62 @ X61)
% 12.00/12.25          | ~ (m1_pre_topc @ X62 @ X61)
% 12.00/12.25          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X62))
% 12.00/12.25          | ~ (r1_tmap_1 @ X62 @ X64 @ (k2_tmap_1 @ X61 @ X64 @ X65 @ X62) @ 
% 12.00/12.25               X63)
% 12.00/12.25          | (r1_tmap_1 @ X61 @ X64 @ X65 @ X66)
% 12.00/12.25          | ((X66) != (X63))
% 12.00/12.25          | ~ (m1_subset_1 @ X66 @ (u1_struct_0 @ X61))
% 12.00/12.25          | ~ (m1_subset_1 @ X65 @ 
% 12.00/12.25               (k1_zfmisc_1 @ 
% 12.00/12.25                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))))
% 12.00/12.25          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))
% 12.00/12.25          | ~ (v1_funct_1 @ X65)
% 12.00/12.25          | ~ (l1_pre_topc @ X64)
% 12.00/12.25          | ~ (v2_pre_topc @ X64)
% 12.00/12.25          | (v2_struct_0 @ X64))),
% 12.00/12.25      inference('cnf', [status(esa)], [t67_tmap_1])).
% 12.00/12.25  thf('129', plain,
% 12.00/12.25      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 12.00/12.25         ((v2_struct_0 @ X64)
% 12.00/12.25          | ~ (v2_pre_topc @ X64)
% 12.00/12.25          | ~ (l1_pre_topc @ X64)
% 12.00/12.25          | ~ (v1_funct_1 @ X65)
% 12.00/12.25          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))
% 12.00/12.25          | ~ (m1_subset_1 @ X65 @ 
% 12.00/12.25               (k1_zfmisc_1 @ 
% 12.00/12.25                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))))
% 12.00/12.25          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X61))
% 12.00/12.25          | (r1_tmap_1 @ X61 @ X64 @ X65 @ X63)
% 12.00/12.25          | ~ (r1_tmap_1 @ X62 @ X64 @ (k2_tmap_1 @ X61 @ X64 @ X65 @ X62) @ 
% 12.00/12.25               X63)
% 12.00/12.25          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X62))
% 12.00/12.25          | ~ (m1_pre_topc @ X62 @ X61)
% 12.00/12.25          | ~ (v1_tsep_1 @ X62 @ X61)
% 12.00/12.25          | (v2_struct_0 @ X62)
% 12.00/12.25          | ~ (l1_pre_topc @ X61)
% 12.00/12.25          | ~ (v2_pre_topc @ X61)
% 12.00/12.25          | (v2_struct_0 @ X61))),
% 12.00/12.25      inference('simplify', [status(thm)], ['128'])).
% 12.00/12.25  thf('130', plain,
% 12.00/12.25      (![X0 : $i, X1 : $i]:
% 12.00/12.25         ((v2_struct_0 @ sk_C_1)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_C_1)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_C_1)
% 12.00/12.25          | (v2_struct_0 @ X0)
% 12.00/12.25          | ~ (v1_tsep_1 @ X0 @ sk_C_1)
% 12.00/12.25          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.00/12.25          | ~ (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 12.00/12.25               (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0) @ X1)
% 12.00/12.25          | (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1)
% 12.00/12.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.25               (u1_struct_0 @ sk_B_2))
% 12.00/12.25          | ~ (v1_funct_1 @ sk_E)
% 12.00/12.25          | ~ (l1_pre_topc @ sk_B_2)
% 12.00/12.25          | ~ (v2_pre_topc @ sk_B_2)
% 12.00/12.25          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.25      inference('sup-', [status(thm)], ['127', '129'])).
% 12.00/12.25  thf('131', plain, ((v2_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['99', '100', '101'])).
% 12.00/12.25  thf('132', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.25      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('133', plain,
% 12.00/12.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['105', '106'])).
% 12.00/12.26  thf('134', plain, ((v1_funct_1 @ sk_E)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('135', plain, ((l1_pre_topc @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('136', plain, ((v2_pre_topc @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('137', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_C_1)
% 12.00/12.26          | (v2_struct_0 @ X0)
% 12.00/12.26          | ~ (v1_tsep_1 @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 12.00/12.26               (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0) @ X1)
% 12.00/12.26          | (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1)
% 12.00/12.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)],
% 12.00/12.26                ['130', '131', '132', '133', '134', '135', '136'])).
% 12.00/12.26  thf('138', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2)
% 12.00/12.26        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26        | (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F)
% 12.00/12.26        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 12.00/12.26        | ~ (v1_tsep_1 @ sk_C_1 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['126', '137'])).
% 12.00/12.26  thf('139', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('140', plain, (((sk_F) = (sk_G))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('141', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['139', '140'])).
% 12.00/12.26  thf('142', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['139', '140'])).
% 12.00/12.26  thf('143', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['22', '27'])).
% 12.00/12.26  thf('144', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('145', plain,
% 12.00/12.26      (![X42 : $i, X43 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X42)
% 12.00/12.26          | ~ (m1_pre_topc @ X43 @ 
% 12.00/12.26               (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)))
% 12.00/12.26          | (m1_pre_topc @ X43 @ X42)
% 12.00/12.26          | ~ (l1_pre_topc @ X43))),
% 12.00/12.26      inference('cnf', [status(esa)], [t65_pre_topc])).
% 12.00/12.26  thf('146', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (l1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['144', '145'])).
% 12.00/12.26  thf('147', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('148', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | (m1_pre_topc @ X0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['146', '147'])).
% 12.00/12.26  thf('149', plain,
% 12.00/12.26      (((m1_pre_topc @ sk_C_1 @ sk_C_1) | ~ (l1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['143', '148'])).
% 12.00/12.26  thf('150', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('151', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['149', '150'])).
% 12.00/12.26  thf('152', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('153', plain,
% 12.00/12.26      (![X2 : $i]:
% 12.00/12.26         (~ (v1_pre_topc @ X2)
% 12.00/12.26          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 12.00/12.26          | ~ (l1_pre_topc @ X2))),
% 12.00/12.26      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 12.00/12.26  thf('154', plain,
% 12.00/12.26      (![X34 : $i]:
% 12.00/12.26         ((m1_subset_1 @ (u1_pre_topc @ X34) @ 
% 12.00/12.26           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 12.00/12.26          | ~ (l1_pre_topc @ X34))),
% 12.00/12.26      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 12.00/12.26  thf('155', plain,
% 12.00/12.26      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 12.00/12.26         (((g1_pre_topc @ X37 @ X38) != (g1_pre_topc @ X35 @ X36))
% 12.00/12.26          | ((X38) = (X36))
% 12.00/12.26          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X37))))),
% 12.00/12.26      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 12.00/12.26  thf('156', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | ((u1_pre_topc @ X0) = (X1))
% 12.00/12.26          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 12.00/12.26              != (g1_pre_topc @ X2 @ X1)))),
% 12.00/12.26      inference('sup-', [status(thm)], ['154', '155'])).
% 12.00/12.26  thf('157', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.00/12.26         (((X0) != (g1_pre_topc @ X2 @ X1))
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v1_pre_topc @ X0)
% 12.00/12.26          | ((u1_pre_topc @ X0) = (X1))
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['153', '156'])).
% 12.00/12.26  thf('158', plain,
% 12.00/12.26      (![X1 : $i, X2 : $i]:
% 12.00/12.26         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 12.00/12.26          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 12.00/12.26          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 12.00/12.26      inference('simplify', [status(thm)], ['157'])).
% 12.00/12.26  thf('159', plain,
% 12.00/12.26      ((~ (v1_pre_topc @ sk_D)
% 12.00/12.26        | ~ (l1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 12.00/12.26        | ((u1_pre_topc @ 
% 12.00/12.26            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 12.00/12.26            = (u1_pre_topc @ sk_C_1)))),
% 12.00/12.26      inference('sup-', [status(thm)], ['152', '158'])).
% 12.00/12.26  thf('160', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('161', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('162', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('163', plain,
% 12.00/12.26      ((~ (v1_pre_topc @ sk_D)
% 12.00/12.26        | ((u1_pre_topc @ sk_D) = (u1_pre_topc @ sk_C_1)))),
% 12.00/12.26      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 12.00/12.26  thf('164', plain, ((v1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['35', '44', '45'])).
% 12.00/12.26  thf('165', plain, (((u1_pre_topc @ sk_D) = (u1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['163', '164'])).
% 12.00/12.26  thf(d1_pre_topc, axiom,
% 12.00/12.26    (![A:$i]:
% 12.00/12.26     ( ( l1_pre_topc @ A ) =>
% 12.00/12.26       ( ( v2_pre_topc @ A ) <=>
% 12.00/12.26         ( ( ![B:$i]:
% 12.00/12.26             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.00/12.26               ( ![C:$i]:
% 12.00/12.26                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.00/12.26                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 12.00/12.26                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 12.00/12.26                     ( r2_hidden @
% 12.00/12.26                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 12.00/12.26                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 12.00/12.26           ( ![B:$i]:
% 12.00/12.26             ( ( m1_subset_1 @
% 12.00/12.26                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.00/12.26               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 12.00/12.26                 ( r2_hidden @
% 12.00/12.26                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 12.00/12.26                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 12.00/12.26           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 12.00/12.26  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 12.00/12.26  thf(zf_stmt_2, axiom,
% 12.00/12.26    (![B:$i,A:$i]:
% 12.00/12.26     ( ( zip_tseitin_5 @ B @ A ) <=>
% 12.00/12.26       ( ( m1_subset_1 @
% 12.00/12.26           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.00/12.26         ( zip_tseitin_4 @ B @ A ) ) ))).
% 12.00/12.26  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 12.00/12.26  thf(zf_stmt_4, axiom,
% 12.00/12.26    (![B:$i,A:$i]:
% 12.00/12.26     ( ( zip_tseitin_4 @ B @ A ) <=>
% 12.00/12.26       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 12.00/12.26         ( r2_hidden @
% 12.00/12.26           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 12.00/12.26  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 12.00/12.26  thf(zf_stmt_6, axiom,
% 12.00/12.26    (![B:$i,A:$i]:
% 12.00/12.26     ( ( zip_tseitin_3 @ B @ A ) <=>
% 12.00/12.26       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.00/12.26         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 12.00/12.26  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 12.00/12.26  thf(zf_stmt_8, axiom,
% 12.00/12.26    (![C:$i,B:$i,A:$i]:
% 12.00/12.26     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 12.00/12.26       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.00/12.26         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 12.00/12.26  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.00/12.26  thf(zf_stmt_10, axiom,
% 12.00/12.26    (![C:$i,B:$i,A:$i]:
% 12.00/12.26     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 12.00/12.26       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 12.00/12.26         ( r2_hidden @
% 12.00/12.26           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 12.00/12.26  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 12.00/12.26  thf(zf_stmt_12, axiom,
% 12.00/12.26    (![C:$i,B:$i,A:$i]:
% 12.00/12.26     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 12.00/12.26       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 12.00/12.26         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 12.00/12.26  thf(zf_stmt_13, axiom,
% 12.00/12.26    (![A:$i]:
% 12.00/12.26     ( ( l1_pre_topc @ A ) =>
% 12.00/12.26       ( ( v2_pre_topc @ A ) <=>
% 12.00/12.26         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 12.00/12.26           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 12.00/12.26           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 12.00/12.26  thf('166', plain,
% 12.00/12.26      (![X27 : $i]:
% 12.00/12.26         (~ (v2_pre_topc @ X27)
% 12.00/12.26          | (r2_hidden @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27))
% 12.00/12.26          | ~ (l1_pre_topc @ X27))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_13])).
% 12.00/12.26  thf('167', plain,
% 12.00/12.26      (((r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26        | ~ (l1_pre_topc @ sk_D)
% 12.00/12.26        | ~ (v2_pre_topc @ sk_D))),
% 12.00/12.26      inference('sup+', [status(thm)], ['165', '166'])).
% 12.00/12.26  thf('168', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('169', plain, ((v2_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['74', '75', '76'])).
% 12.00/12.26  thf('170', plain,
% 12.00/12.26      ((r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['167', '168', '169'])).
% 12.00/12.26  thf('171', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('172', plain,
% 12.00/12.26      ((r2_hidden @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['170', '171'])).
% 12.00/12.26  thf(dt_k2_subset_1, axiom,
% 12.00/12.26    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 12.00/12.26  thf('173', plain,
% 12.00/12.26      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 12.00/12.26      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 12.00/12.26  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 12.00/12.26  thf('174', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 12.00/12.26      inference('cnf', [status(esa)], [d4_subset_1])).
% 12.00/12.26  thf('175', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.00/12.26      inference('demod', [status(thm)], ['173', '174'])).
% 12.00/12.26  thf(d5_pre_topc, axiom,
% 12.00/12.26    (![A:$i]:
% 12.00/12.26     ( ( l1_pre_topc @ A ) =>
% 12.00/12.26       ( ![B:$i]:
% 12.00/12.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.00/12.26           ( ( v3_pre_topc @ B @ A ) <=>
% 12.00/12.26             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 12.00/12.26  thf('176', plain,
% 12.00/12.26      (![X30 : $i, X31 : $i]:
% 12.00/12.26         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 12.00/12.26          | ~ (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 12.00/12.26          | (v3_pre_topc @ X30 @ X31)
% 12.00/12.26          | ~ (l1_pre_topc @ X31))),
% 12.00/12.26      inference('cnf', [status(esa)], [d5_pre_topc])).
% 12.00/12.26  thf('177', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.00/12.26          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 12.00/12.26      inference('sup-', [status(thm)], ['175', '176'])).
% 12.00/12.26  thf('178', plain,
% 12.00/12.26      (((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_C_1)
% 12.00/12.26        | ~ (l1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['172', '177'])).
% 12.00/12.26  thf('179', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('180', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['178', '179'])).
% 12.00/12.26  thf('181', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.00/12.26      inference('demod', [status(thm)], ['173', '174'])).
% 12.00/12.26  thf(t16_tsep_1, axiom,
% 12.00/12.26    (![A:$i]:
% 12.00/12.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.00/12.26       ( ![B:$i]:
% 12.00/12.26         ( ( m1_pre_topc @ B @ A ) =>
% 12.00/12.26           ( ![C:$i]:
% 12.00/12.26             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.00/12.26               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 12.00/12.26                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 12.00/12.26                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 12.00/12.26  thf('182', plain,
% 12.00/12.26      (![X55 : $i, X56 : $i, X57 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X55 @ X56)
% 12.00/12.26          | ((X57) != (u1_struct_0 @ X55))
% 12.00/12.26          | ~ (v3_pre_topc @ X57 @ X56)
% 12.00/12.26          | (v1_tsep_1 @ X55 @ X56)
% 12.00/12.26          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 12.00/12.26          | ~ (l1_pre_topc @ X56)
% 12.00/12.26          | ~ (v2_pre_topc @ X56))),
% 12.00/12.26      inference('cnf', [status(esa)], [t16_tsep_1])).
% 12.00/12.26  thf('183', plain,
% 12.00/12.26      (![X55 : $i, X56 : $i]:
% 12.00/12.26         (~ (v2_pre_topc @ X56)
% 12.00/12.26          | ~ (l1_pre_topc @ X56)
% 12.00/12.26          | ~ (m1_subset_1 @ (u1_struct_0 @ X55) @ 
% 12.00/12.26               (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 12.00/12.26          | (v1_tsep_1 @ X55 @ X56)
% 12.00/12.26          | ~ (v3_pre_topc @ (u1_struct_0 @ X55) @ X56)
% 12.00/12.26          | ~ (m1_pre_topc @ X55 @ X56))),
% 12.00/12.26      inference('simplify', [status(thm)], ['182'])).
% 12.00/12.26  thf('184', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X0 @ X0)
% 12.00/12.26          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.00/12.26          | (v1_tsep_1 @ X0 @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['181', '183'])).
% 12.00/12.26  thf('185', plain,
% 12.00/12.26      ((~ (v2_pre_topc @ sk_C_1)
% 12.00/12.26        | ~ (l1_pre_topc @ sk_C_1)
% 12.00/12.26        | (v1_tsep_1 @ sk_C_1 @ sk_C_1)
% 12.00/12.26        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['180', '184'])).
% 12.00/12.26  thf('186', plain, ((v2_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['99', '100', '101'])).
% 12.00/12.26  thf('187', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('188', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['149', '150'])).
% 12.00/12.26  thf('189', plain, ((v1_tsep_1 @ sk_C_1 @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 12.00/12.26  thf('190', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2)
% 12.00/12.26        | (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['138', '141', '142', '151', '189'])).
% 12.00/12.26  thf('191', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('simplify', [status(thm)], ['190'])).
% 12.00/12.26  thf('192', plain, (~ (v2_struct_0 @ sk_C_1)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('193', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2) | (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F))),
% 12.00/12.26      inference('clc', [status(thm)], ['191', '192'])).
% 12.00/12.26  thf('194', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('195', plain, ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_F)),
% 12.00/12.26      inference('clc', [status(thm)], ['193', '194'])).
% 12.00/12.26  thf('196', plain,
% 12.00/12.26      ((m1_subset_1 @ sk_E @ 
% 12.00/12.26        (k1_zfmisc_1 @ 
% 12.00/12.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.26      inference('demod', [status(thm)], ['92', '93'])).
% 12.00/12.26  thf('197', plain,
% 12.00/12.26      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 12.00/12.26         ((v2_struct_0 @ X61)
% 12.00/12.26          | ~ (v2_pre_topc @ X61)
% 12.00/12.26          | ~ (l1_pre_topc @ X61)
% 12.00/12.26          | (v2_struct_0 @ X62)
% 12.00/12.26          | ~ (v1_tsep_1 @ X62 @ X61)
% 12.00/12.26          | ~ (m1_pre_topc @ X62 @ X61)
% 12.00/12.26          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X62))
% 12.00/12.26          | ~ (r1_tmap_1 @ X61 @ X64 @ X65 @ X66)
% 12.00/12.26          | (r1_tmap_1 @ X62 @ X64 @ (k2_tmap_1 @ X61 @ X64 @ X65 @ X62) @ X63)
% 12.00/12.26          | ((X66) != (X63))
% 12.00/12.26          | ~ (m1_subset_1 @ X66 @ (u1_struct_0 @ X61))
% 12.00/12.26          | ~ (m1_subset_1 @ X65 @ 
% 12.00/12.26               (k1_zfmisc_1 @ 
% 12.00/12.26                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))))
% 12.00/12.26          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))
% 12.00/12.26          | ~ (v1_funct_1 @ X65)
% 12.00/12.26          | ~ (l1_pre_topc @ X64)
% 12.00/12.26          | ~ (v2_pre_topc @ X64)
% 12.00/12.26          | (v2_struct_0 @ X64))),
% 12.00/12.26      inference('cnf', [status(esa)], [t67_tmap_1])).
% 12.00/12.26  thf('198', plain,
% 12.00/12.26      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 12.00/12.26         ((v2_struct_0 @ X64)
% 12.00/12.26          | ~ (v2_pre_topc @ X64)
% 12.00/12.26          | ~ (l1_pre_topc @ X64)
% 12.00/12.26          | ~ (v1_funct_1 @ X65)
% 12.00/12.26          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))
% 12.00/12.26          | ~ (m1_subset_1 @ X65 @ 
% 12.00/12.26               (k1_zfmisc_1 @ 
% 12.00/12.26                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))))
% 12.00/12.26          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X61))
% 12.00/12.26          | (r1_tmap_1 @ X62 @ X64 @ (k2_tmap_1 @ X61 @ X64 @ X65 @ X62) @ X63)
% 12.00/12.26          | ~ (r1_tmap_1 @ X61 @ X64 @ X65 @ X63)
% 12.00/12.26          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X62))
% 12.00/12.26          | ~ (m1_pre_topc @ X62 @ X61)
% 12.00/12.26          | ~ (v1_tsep_1 @ X62 @ X61)
% 12.00/12.26          | (v2_struct_0 @ X62)
% 12.00/12.26          | ~ (l1_pre_topc @ X61)
% 12.00/12.26          | ~ (v2_pre_topc @ X61)
% 12.00/12.26          | (v2_struct_0 @ X61))),
% 12.00/12.26      inference('simplify', [status(thm)], ['197'])).
% 12.00/12.26  thf('199', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_C_1)
% 12.00/12.26          | ~ (v2_pre_topc @ sk_C_1)
% 12.00/12.26          | ~ (l1_pre_topc @ sk_C_1)
% 12.00/12.26          | (v2_struct_0 @ X0)
% 12.00/12.26          | ~ (v1_tsep_1 @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1)
% 12.00/12.26          | (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 12.00/12.26             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0) @ X1)
% 12.00/12.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.26               (u1_struct_0 @ sk_B_2))
% 12.00/12.26          | ~ (v1_funct_1 @ sk_E)
% 12.00/12.26          | ~ (l1_pre_topc @ sk_B_2)
% 12.00/12.26          | ~ (v2_pre_topc @ sk_B_2)
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('sup-', [status(thm)], ['196', '198'])).
% 12.00/12.26  thf('200', plain, ((v2_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['99', '100', '101'])).
% 12.00/12.26  thf('201', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('202', plain,
% 12.00/12.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['105', '106'])).
% 12.00/12.26  thf('203', plain, ((v1_funct_1 @ sk_E)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('204', plain, ((l1_pre_topc @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('205', plain, ((v2_pre_topc @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('206', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_C_1)
% 12.00/12.26          | (v2_struct_0 @ X0)
% 12.00/12.26          | ~ (v1_tsep_1 @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X1)
% 12.00/12.26          | (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 12.00/12.26             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0) @ X1)
% 12.00/12.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)],
% 12.00/12.26                ['199', '200', '201', '202', '203', '204', '205'])).
% 12.00/12.26  thf('207', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_B_2)
% 12.00/12.26          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 12.00/12.26             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0) @ sk_F)
% 12.00/12.26          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (v1_tsep_1 @ X0 @ sk_C_1)
% 12.00/12.26          | (v2_struct_0 @ X0)
% 12.00/12.26          | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['195', '206'])).
% 12.00/12.26  thf('208', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['139', '140'])).
% 12.00/12.26  thf('209', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_B_2)
% 12.00/12.26          | (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 12.00/12.26             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0) @ sk_F)
% 12.00/12.26          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | ~ (v1_tsep_1 @ X0 @ sk_C_1)
% 12.00/12.26          | (v2_struct_0 @ X0)
% 12.00/12.26          | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['207', '208'])).
% 12.00/12.26  thf('210', plain,
% 12.00/12.26      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26        | (v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | ~ (v1_tsep_1 @ sk_D @ sk_C_1)
% 12.00/12.26        | ~ (m1_pre_topc @ sk_D @ sk_C_1)
% 12.00/12.26        | (r1_tmap_1 @ sk_D @ sk_B_2 @ 
% 12.00/12.26           (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D) @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('sup-', [status(thm)], ['47', '209'])).
% 12.00/12.26  thf('211', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['139', '140'])).
% 12.00/12.26  thf('212', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('213', plain,
% 12.00/12.26      (![X60 : $i]: ((m1_pre_topc @ X60 @ X60) | ~ (l1_pre_topc @ X60))),
% 12.00/12.26      inference('cnf', [status(esa)], [t2_tsep_1])).
% 12.00/12.26  thf('214', plain,
% 12.00/12.26      (![X53 : $i, X54 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X53 @ X54)
% 12.00/12.26          | (m1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X53) @ (u1_pre_topc @ X53)) @ X54)
% 12.00/12.26          | ~ (l1_pre_topc @ X54))),
% 12.00/12.26      inference('cnf', [status(esa)], [t11_tmap_1])).
% 12.00/12.26  thf('215', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | (m1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['213', '214'])).
% 12.00/12.26  thf('216', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((m1_pre_topc @ 
% 12.00/12.26           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('simplify', [status(thm)], ['215'])).
% 12.00/12.26  thf(t1_tsep_1, axiom,
% 12.00/12.26    (![A:$i]:
% 12.00/12.26     ( ( l1_pre_topc @ A ) =>
% 12.00/12.26       ( ![B:$i]:
% 12.00/12.26         ( ( m1_pre_topc @ B @ A ) =>
% 12.00/12.26           ( m1_subset_1 @
% 12.00/12.26             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 12.00/12.26  thf('217', plain,
% 12.00/12.26      (![X58 : $i, X59 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X58 @ X59)
% 12.00/12.26          | (m1_subset_1 @ (u1_struct_0 @ X58) @ 
% 12.00/12.26             (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 12.00/12.26          | ~ (l1_pre_topc @ X59))),
% 12.00/12.26      inference('cnf', [status(esa)], [t1_tsep_1])).
% 12.00/12.26  thf('218', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | (m1_subset_1 @ 
% 12.00/12.26             (u1_struct_0 @ 
% 12.00/12.26              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 12.00/12.26             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 12.00/12.26      inference('sup-', [status(thm)], ['216', '217'])).
% 12.00/12.26  thf('219', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((m1_subset_1 @ 
% 12.00/12.26           (u1_struct_0 @ 
% 12.00/12.26            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 12.00/12.26           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('simplify', [status(thm)], ['218'])).
% 12.00/12.26  thf('220', plain,
% 12.00/12.26      (![X55 : $i, X56 : $i]:
% 12.00/12.26         (~ (v2_pre_topc @ X56)
% 12.00/12.26          | ~ (l1_pre_topc @ X56)
% 12.00/12.26          | ~ (m1_subset_1 @ (u1_struct_0 @ X55) @ 
% 12.00/12.26               (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 12.00/12.26          | (v1_tsep_1 @ X55 @ X56)
% 12.00/12.26          | ~ (v3_pre_topc @ (u1_struct_0 @ X55) @ X56)
% 12.00/12.26          | ~ (m1_pre_topc @ X55 @ X56))),
% 12.00/12.26      inference('simplify', [status(thm)], ['182'])).
% 12.00/12.26  thf('221', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (m1_pre_topc @ 
% 12.00/12.26               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (v3_pre_topc @ 
% 12.00/12.26               (u1_struct_0 @ 
% 12.00/12.26                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 12.00/12.26               X0)
% 12.00/12.26          | (v1_tsep_1 @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['219', '220'])).
% 12.00/12.26  thf('222', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (v2_pre_topc @ X0)
% 12.00/12.26          | (v1_tsep_1 @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (v3_pre_topc @ 
% 12.00/12.26               (u1_struct_0 @ 
% 12.00/12.26                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 12.00/12.26               X0)
% 12.00/12.26          | ~ (m1_pre_topc @ 
% 12.00/12.26               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('simplify', [status(thm)], ['221'])).
% 12.00/12.26  thf('223', plain,
% 12.00/12.26      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C_1)
% 12.00/12.26        | ~ (l1_pre_topc @ sk_C_1)
% 12.00/12.26        | ~ (m1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 12.00/12.26             sk_C_1)
% 12.00/12.26        | (v1_tsep_1 @ 
% 12.00/12.26           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 12.00/12.26           sk_C_1)
% 12.00/12.26        | ~ (v2_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['212', '222'])).
% 12.00/12.26  thf('224', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('225', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['178', '179'])).
% 12.00/12.26  thf('226', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('227', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('228', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('229', plain,
% 12.00/12.26      (![X60 : $i]: ((m1_pre_topc @ X60 @ X60) | ~ (l1_pre_topc @ X60))),
% 12.00/12.26      inference('cnf', [status(esa)], [t2_tsep_1])).
% 12.00/12.26  thf('230', plain,
% 12.00/12.26      (![X42 : $i, X43 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X42)
% 12.00/12.26          | ~ (m1_pre_topc @ X43 @ 
% 12.00/12.26               (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)))
% 12.00/12.26          | (m1_pre_topc @ X43 @ X42)
% 12.00/12.26          | ~ (l1_pre_topc @ X43))),
% 12.00/12.26      inference('cnf', [status(esa)], [t65_pre_topc])).
% 12.00/12.26  thf('231', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 12.00/12.26          | ~ (l1_pre_topc @ 
% 12.00/12.26               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 12.00/12.26          | (m1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['229', '230'])).
% 12.00/12.26  thf('232', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | (m1_pre_topc @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ 
% 12.00/12.26               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 12.00/12.26      inference('simplify', [status(thm)], ['231'])).
% 12.00/12.26  thf('233', plain,
% 12.00/12.26      ((~ (l1_pre_topc @ sk_D)
% 12.00/12.26        | (m1_pre_topc @ 
% 12.00/12.26           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 12.00/12.26           sk_C_1)
% 12.00/12.26        | ~ (l1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['228', '232'])).
% 12.00/12.26  thf('234', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('235', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('236', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('237', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 12.00/12.26  thf('238', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('239', plain, ((v2_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['99', '100', '101'])).
% 12.00/12.26  thf('240', plain, ((v1_tsep_1 @ sk_D @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)],
% 12.00/12.26                ['223', '224', '225', '226', '227', '237', '238', '239'])).
% 12.00/12.26  thf('241', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 12.00/12.26  thf('242', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((m1_pre_topc @ 
% 12.00/12.26           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('simplify', [status(thm)], ['215'])).
% 12.00/12.26  thf('243', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_C_1)
% 12.00/12.26          | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.26                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)],
% 12.00/12.26                ['96', '102', '103', '104', '107', '108', '109'])).
% 12.00/12.26  thf('244', plain,
% 12.00/12.26      ((~ (l1_pre_topc @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2)
% 12.00/12.26        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ 
% 12.00/12.26            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 12.00/12.26            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26               sk_E @ 
% 12.00/12.26               (u1_struct_0 @ 
% 12.00/12.26                (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))))
% 12.00/12.26        | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['242', '243'])).
% 12.00/12.26  thf('245', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('246', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('247', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('248', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('249', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 12.00/12.26      inference('clc', [status(thm)], ['88', '89'])).
% 12.00/12.26  thf('250', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2)
% 12.00/12.26        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26            = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))
% 12.00/12.26        | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)],
% 12.00/12.26                ['244', '245', '246', '247', '248', '249'])).
% 12.00/12.26  thf('251', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('252', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_C_1)
% 12.00/12.26        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26            = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)))),
% 12.00/12.26      inference('clc', [status(thm)], ['250', '251'])).
% 12.00/12.26  thf('253', plain, (~ (v2_struct_0 @ sk_C_1)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('254', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))),
% 12.00/12.26      inference('clc', [status(thm)], ['252', '253'])).
% 12.00/12.26  thf('255', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))),
% 12.00/12.26      inference('clc', [status(thm)], ['116', '117'])).
% 12.00/12.26  thf('256', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_D))),
% 12.00/12.26      inference('sup+', [status(thm)], ['254', '255'])).
% 12.00/12.26  thf('257', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | (r1_tmap_1 @ sk_D @ sk_B_2 @ 
% 12.00/12.26           (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['210', '211', '240', '241', '256'])).
% 12.00/12.26  thf('258', plain,
% 12.00/12.26      (![X60 : $i]: ((m1_pre_topc @ X60 @ X60) | ~ (l1_pre_topc @ X60))),
% 12.00/12.26      inference('cnf', [status(esa)], [t2_tsep_1])).
% 12.00/12.26  thf('259', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_D)
% 12.00/12.26          | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.26                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 12.00/12.26          | ~ (m1_pre_topc @ X0 @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['83', '84'])).
% 12.00/12.26  thf('260', plain,
% 12.00/12.26      ((~ (l1_pre_topc @ sk_D)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2)
% 12.00/12.26        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26               sk_E @ (u1_struct_0 @ sk_D)))
% 12.00/12.26        | (v2_struct_0 @ sk_D))),
% 12.00/12.26      inference('sup-', [status(thm)], ['258', '259'])).
% 12.00/12.26  thf('261', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('262', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('263', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2)
% 12.00/12.26        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26               sk_E @ (u1_struct_0 @ sk_C_1)))
% 12.00/12.26        | (v2_struct_0 @ sk_D))),
% 12.00/12.26      inference('demod', [status(thm)], ['260', '261', '262'])).
% 12.00/12.26  thf('264', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('265', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_D)
% 12.00/12.26        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 12.00/12.26      inference('clc', [status(thm)], ['263', '264'])).
% 12.00/12.26  thf('266', plain, (~ (v2_struct_0 @ sk_D)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('267', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D)
% 12.00/12.26         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 12.00/12.26      inference('clc', [status(thm)], ['265', '266'])).
% 12.00/12.26  thf('268', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 12.00/12.26            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 12.00/12.26      inference('clc', [status(thm)], ['88', '89'])).
% 12.00/12.26  thf('269', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D))),
% 12.00/12.26      inference('sup+', [status(thm)], ['267', '268'])).
% 12.00/12.26  thf('270', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))),
% 12.00/12.26      inference('clc', [status(thm)], ['116', '117'])).
% 12.00/12.26  thf('271', plain,
% 12.00/12.26      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 12.00/12.26         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_D))),
% 12.00/12.26      inference('demod', [status(thm)], ['269', '270'])).
% 12.00/12.26  thf('272', plain,
% 12.00/12.26      ((m1_subset_1 @ sk_E @ 
% 12.00/12.26        (k1_zfmisc_1 @ 
% 12.00/12.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 12.00/12.26      inference('demod', [status(thm)], ['92', '93'])).
% 12.00/12.26  thf('273', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('274', plain,
% 12.00/12.26      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 12.00/12.26         ((v2_struct_0 @ X64)
% 12.00/12.26          | ~ (v2_pre_topc @ X64)
% 12.00/12.26          | ~ (l1_pre_topc @ X64)
% 12.00/12.26          | ~ (v1_funct_1 @ X65)
% 12.00/12.26          | ~ (v1_funct_2 @ X65 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))
% 12.00/12.26          | ~ (m1_subset_1 @ X65 @ 
% 12.00/12.26               (k1_zfmisc_1 @ 
% 12.00/12.26                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X64))))
% 12.00/12.26          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X61))
% 12.00/12.26          | (r1_tmap_1 @ X61 @ X64 @ X65 @ X63)
% 12.00/12.26          | ~ (r1_tmap_1 @ X62 @ X64 @ (k2_tmap_1 @ X61 @ X64 @ X65 @ X62) @ 
% 12.00/12.26               X63)
% 12.00/12.26          | ~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X62))
% 12.00/12.26          | ~ (m1_pre_topc @ X62 @ X61)
% 12.00/12.26          | ~ (v1_tsep_1 @ X62 @ X61)
% 12.00/12.26          | (v2_struct_0 @ X62)
% 12.00/12.26          | ~ (l1_pre_topc @ X61)
% 12.00/12.26          | ~ (v2_pre_topc @ X61)
% 12.00/12.26          | (v2_struct_0 @ X61))),
% 12.00/12.26      inference('simplify', [status(thm)], ['128'])).
% 12.00/12.26  thf('275', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.00/12.26         (~ (m1_subset_1 @ X1 @ 
% 12.00/12.26             (k1_zfmisc_1 @ 
% 12.00/12.26              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | ~ (v2_pre_topc @ sk_D)
% 12.00/12.26          | ~ (l1_pre_topc @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ X2)
% 12.00/12.26          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 12.00/12.26          | ~ (m1_pre_topc @ X2 @ sk_D)
% 12.00/12.26          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 12.00/12.26          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 12.00/12.26          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 12.00/12.26          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (v1_funct_1 @ X1)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0)
% 12.00/12.26          | (v2_struct_0 @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['273', '274'])).
% 12.00/12.26  thf('276', plain, ((v2_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['74', '75', '76'])).
% 12.00/12.26  thf('277', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('278', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('279', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('280', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.00/12.26         (~ (m1_subset_1 @ X1 @ 
% 12.00/12.26             (k1_zfmisc_1 @ 
% 12.00/12.26              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ X2)
% 12.00/12.26          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 12.00/12.26          | ~ (m1_pre_topc @ X2 @ sk_D)
% 12.00/12.26          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 12.00/12.26          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 12.00/12.26          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 12.00/12.26          | ~ (v1_funct_1 @ X1)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0)
% 12.00/12.26          | (v2_struct_0 @ X0))),
% 12.00/12.26      inference('demod', [status(thm)], ['275', '276', '277', '278', '279'])).
% 12.00/12.26  thf('281', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_B_2)
% 12.00/12.26          | ~ (v2_pre_topc @ sk_B_2)
% 12.00/12.26          | ~ (l1_pre_topc @ sk_B_2)
% 12.00/12.26          | ~ (v1_funct_1 @ sk_E)
% 12.00/12.26          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 12.00/12.26               (u1_struct_0 @ sk_B_2))
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 12.00/12.26               (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X1) @ X0)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 12.00/12.26          | ~ (m1_pre_topc @ X1 @ sk_D)
% 12.00/12.26          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ X1)
% 12.00/12.26          | (v2_struct_0 @ sk_D))),
% 12.00/12.26      inference('sup-', [status(thm)], ['272', '280'])).
% 12.00/12.26  thf('282', plain, ((v2_pre_topc @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('283', plain, ((l1_pre_topc @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('284', plain, ((v1_funct_1 @ sk_E)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('285', plain,
% 12.00/12.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['105', '106'])).
% 12.00/12.26  thf('286', plain,
% 12.00/12.26      (![X0 : $i, X1 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_B_2)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 12.00/12.26               (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X1) @ X0)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 12.00/12.26          | ~ (m1_pre_topc @ X1 @ sk_D)
% 12.00/12.26          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ X1)
% 12.00/12.26          | (v2_struct_0 @ sk_D))),
% 12.00/12.26      inference('demod', [status(thm)], ['281', '282', '283', '284', '285'])).
% 12.00/12.26  thf('287', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ 
% 12.00/12.26             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ X0)
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 12.00/12.26          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('sup-', [status(thm)], ['271', '286'])).
% 12.00/12.26  thf('288', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('289', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (m1_pre_topc @ X0 @ X0)
% 12.00/12.26          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.00/12.26          | (v1_tsep_1 @ X0 @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['181', '183'])).
% 12.00/12.26  thf('290', plain,
% 12.00/12.26      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 12.00/12.26        | ~ (v2_pre_topc @ sk_D)
% 12.00/12.26        | ~ (l1_pre_topc @ sk_D)
% 12.00/12.26        | (v1_tsep_1 @ sk_D @ sk_D)
% 12.00/12.26        | ~ (m1_pre_topc @ sk_D @ sk_D))),
% 12.00/12.26      inference('sup-', [status(thm)], ['288', '289'])).
% 12.00/12.26  thf('291', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('292', plain,
% 12.00/12.26      (![X27 : $i]:
% 12.00/12.26         (~ (v2_pre_topc @ X27)
% 12.00/12.26          | (r2_hidden @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27))
% 12.00/12.26          | ~ (l1_pre_topc @ X27))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_13])).
% 12.00/12.26  thf('293', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.00/12.26          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 12.00/12.26      inference('sup-', [status(thm)], ['175', '176'])).
% 12.00/12.26  thf('294', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0)
% 12.00/12.26          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('sup-', [status(thm)], ['292', '293'])).
% 12.00/12.26  thf('295', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 12.00/12.26          | ~ (v2_pre_topc @ X0)
% 12.00/12.26          | ~ (l1_pre_topc @ X0))),
% 12.00/12.26      inference('simplify', [status(thm)], ['294'])).
% 12.00/12.26  thf('296', plain,
% 12.00/12.26      (((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 12.00/12.26        | ~ (l1_pre_topc @ sk_D)
% 12.00/12.26        | ~ (v2_pre_topc @ sk_D))),
% 12.00/12.26      inference('sup+', [status(thm)], ['291', '295'])).
% 12.00/12.26  thf('297', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('298', plain, ((v2_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['74', '75', '76'])).
% 12.00/12.26  thf('299', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['296', '297', '298'])).
% 12.00/12.26  thf('300', plain, ((v2_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['74', '75', '76'])).
% 12.00/12.26  thf('301', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('302', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 12.00/12.26  thf('303', plain,
% 12.00/12.26      (![X42 : $i, X43 : $i]:
% 12.00/12.26         (~ (l1_pre_topc @ X42)
% 12.00/12.26          | ~ (m1_pre_topc @ X43 @ X42)
% 12.00/12.26          | (m1_pre_topc @ X43 @ 
% 12.00/12.26             (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)))
% 12.00/12.26          | ~ (l1_pre_topc @ X43))),
% 12.00/12.26      inference('cnf', [status(esa)], [t65_pre_topc])).
% 12.00/12.26  thf('304', plain,
% 12.00/12.26      ((~ (l1_pre_topc @ sk_D)
% 12.00/12.26        | (m1_pre_topc @ sk_D @ 
% 12.00/12.26           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 12.00/12.26        | ~ (l1_pre_topc @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['302', '303'])).
% 12.00/12.26  thf('305', plain, ((l1_pre_topc @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['12', '13'])).
% 12.00/12.26  thf('306', plain,
% 12.00/12.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 12.00/12.26         = (sk_D))),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('307', plain, ((l1_pre_topc @ sk_C_1)),
% 12.00/12.26      inference('demod', [status(thm)], ['25', '26'])).
% 12.00/12.26  thf('308', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['304', '305', '306', '307'])).
% 12.00/12.26  thf('309', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['290', '299', '300', '301', '308'])).
% 12.00/12.26  thf('310', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 12.00/12.26      inference('demod', [status(thm)], ['304', '305', '306', '307'])).
% 12.00/12.26  thf('311', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['16', '46'])).
% 12.00/12.26  thf('312', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ 
% 12.00/12.26             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ X0)
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['287', '309', '310', '311'])).
% 12.00/12.26  thf('313', plain,
% 12.00/12.26      (![X0 : $i]:
% 12.00/12.26         ((v2_struct_0 @ sk_B_2)
% 12.00/12.26          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 12.00/12.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26          | (v2_struct_0 @ sk_D)
% 12.00/12.26          | ~ (r1_tmap_1 @ sk_D @ sk_B_2 @ 
% 12.00/12.26               (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ X0))),
% 12.00/12.26      inference('simplify', [status(thm)], ['312'])).
% 12.00/12.26  thf('314', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 12.00/12.26        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('sup-', [status(thm)], ['257', '313'])).
% 12.00/12.26  thf('315', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('demod', [status(thm)], ['139', '140'])).
% 12.00/12.26  thf('316', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('demod', [status(thm)], ['314', '315'])).
% 12.00/12.26  thf('317', plain,
% 12.00/12.26      (((r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 12.00/12.26        | (v2_struct_0 @ sk_C_1)
% 12.00/12.26        | (v2_struct_0 @ sk_D)
% 12.00/12.26        | (v2_struct_0 @ sk_B_2))),
% 12.00/12.26      inference('simplify', [status(thm)], ['316'])).
% 12.00/12.26  thf('318', plain, (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('319', plain,
% 12.00/12.26      (((v2_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 12.00/12.26      inference('sup-', [status(thm)], ['317', '318'])).
% 12.00/12.26  thf('320', plain, (~ (v2_struct_0 @ sk_B_2)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('321', plain, (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D))),
% 12.00/12.26      inference('clc', [status(thm)], ['319', '320'])).
% 12.00/12.26  thf('322', plain, (~ (v2_struct_0 @ sk_C_1)),
% 12.00/12.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.00/12.26  thf('323', plain, ((v2_struct_0 @ sk_D)),
% 12.00/12.26      inference('clc', [status(thm)], ['321', '322'])).
% 12.00/12.26  thf('324', plain, ($false), inference('demod', [status(thm)], ['0', '323'])).
% 12.00/12.26  
% 12.00/12.26  % SZS output end Refutation
% 12.00/12.26  
% 12.00/12.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
