%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pOVEIGIXo6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:30 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  251 (2423 expanded)
%              Number of leaves         :   65 ( 740 expanded)
%              Depth                    :   27
%              Number of atoms          : 2547 (67432 expanded)
%              Number of equality atoms :   63 (1794 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('6',plain,(
    ! [X57: $i] :
      ( ( m1_pre_topc @ X57 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ( m1_pre_topc @ X42 @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( l1_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X57: $i] :
      ( ( m1_pre_topc @ X57 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X39 @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) )
      | ( m1_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( l1_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['22','27','28','29'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_pre_topc @ X58 @ X59 )
      | ( r1_tarski @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X59 ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('34',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('39',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_pre_topc @ X58 @ X59 )
      | ( r1_tarski @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X59 ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('45',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['17','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

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

thf('49',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_pre_topc @ X48 @ X49 )
      | ~ ( m1_pre_topc @ X48 @ X50 )
      | ( ( k3_tmap_1 @ X49 @ X47 @ X50 @ X48 @ X51 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X47 ) @ X51 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X47 ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( m1_pre_topc @ X50 @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('59',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['16','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('64',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X39 @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) )
      | ( m1_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['17','46'])).

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

thf('71',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( ( k2_tmap_1 @ X45 @ X43 @ X46 @ X44 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) @ X46 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('72',plain,(
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
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('75',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('82',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['72','78','79','80','81','82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
        = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(demod,[status(thm)],['3','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['17','46'])).

thf('103',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('104',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( ( k2_tmap_1 @ X45 @ X43 @ X46 @ X44 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) @ X46 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('108',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('113',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('114',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','111','112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['101','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('128',plain,
    ( ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 )
    = ( k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['17','46'])).

thf('130',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

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

thf('131',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( v2_struct_0 @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ~ ( l1_pre_topc @ X60 )
      | ( v2_struct_0 @ X61 )
      | ~ ( v1_tsep_1 @ X61 @ X60 )
      | ~ ( m1_pre_topc @ X61 @ X60 )
      | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ X61 ) )
      | ~ ( r1_tmap_1 @ X61 @ X63 @ ( k2_tmap_1 @ X60 @ X63 @ X64 @ X61 ) @ X62 )
      | ( r1_tmap_1 @ X60 @ X63 @ X64 @ X65 )
      | ( X65 != X62 )
      | ~ ( m1_subset_1 @ X65 @ ( u1_struct_0 @ X60 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X63 ) ) ) )
      | ~ ( v1_funct_2 @ X64 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X63 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( l1_pre_topc @ X63 )
      | ~ ( v2_pre_topc @ X63 )
      | ( v2_struct_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('132',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( v2_struct_0 @ X63 )
      | ~ ( v2_pre_topc @ X63 )
      | ~ ( l1_pre_topc @ X63 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X63 ) ) ) )
      | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ X60 ) )
      | ( r1_tmap_1 @ X60 @ X63 @ X64 @ X62 )
      | ~ ( r1_tmap_1 @ X61 @ X63 @ ( k2_tmap_1 @ X60 @ X63 @ X64 @ X61 ) @ X62 )
      | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ X61 ) )
      | ~ ( m1_pre_topc @ X61 @ X60 )
      | ~ ( v1_tsep_1 @ X61 @ X60 )
      | ( v2_struct_0 @ X61 )
      | ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ( v2_struct_0 @ X60 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
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
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('135',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('137',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('138',plain,(
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
    inference(demod,[status(thm)],['133','134','135','136','137'])).

thf('139',plain,(
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
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('144',plain,(
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
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['128','144'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('146',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('147',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('148',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

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

thf('150',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_pre_topc @ X52 @ X53 )
      | ( X54
       != ( u1_struct_0 @ X52 ) )
      | ~ ( v3_pre_topc @ X54 @ X53 )
      | ( v1_tsep_1 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('151',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v2_pre_topc @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( v1_tsep_1 @ X52 @ X53 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X52 ) @ X53 )
      | ~ ( m1_pre_topc @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['149','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('154',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','45'])).

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

thf('158',plain,(
    ! [X29: $i] :
      ( ~ ( v2_pre_topc @ X29 )
      | ( r2_hidden @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('159',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('160',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r2_hidden @ X32 @ ( u1_pre_topc @ X33 ) )
      | ( v3_pre_topc @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['157','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('166',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('167',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('169',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['156','167','168'])).

thf('170',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['145','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['100','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('178',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['0','183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pOVEIGIXo6
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.66/2.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.66/2.86  % Solved by: fo/fo7.sh
% 2.66/2.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.86  % done 2020 iterations in 2.392s
% 2.66/2.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.66/2.86  % SZS output start Refutation
% 2.66/2.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.66/2.86  thf(sk_F_type, type, sk_F: $i).
% 2.66/2.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 2.66/2.86  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.66/2.86  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 2.66/2.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.66/2.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.66/2.86  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 2.66/2.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.66/2.86  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.86  thf(sk_G_type, type, sk_G: $i).
% 2.66/2.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.66/2.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.66/2.86  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 2.66/2.86  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 2.66/2.86  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.66/2.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.66/2.86  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 2.66/2.86  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.66/2.86  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.66/2.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.66/2.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.66/2.86  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 2.66/2.86  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 2.66/2.86  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.66/2.86  thf(sk_E_type, type, sk_E: $i).
% 2.66/2.86  thf(sk_D_type, type, sk_D: $i).
% 2.66/2.86  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 2.66/2.86  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 2.66/2.86  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 2.66/2.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.66/2.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.66/2.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.66/2.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.66/2.86  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.66/2.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.66/2.86  thf(t88_tmap_1, conjecture,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.66/2.86             ( l1_pre_topc @ B ) ) =>
% 2.66/2.86           ( ![C:$i]:
% 2.66/2.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.66/2.86               ( ![D:$i]:
% 2.66/2.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.66/2.86                   ( ![E:$i]:
% 2.66/2.86                     ( ( ( v1_funct_1 @ E ) & 
% 2.66/2.86                         ( v1_funct_2 @
% 2.66/2.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.66/2.86                         ( m1_subset_1 @
% 2.66/2.86                           E @ 
% 2.66/2.86                           ( k1_zfmisc_1 @
% 2.66/2.86                             ( k2_zfmisc_1 @
% 2.66/2.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.66/2.86                       ( ( ( g1_pre_topc @
% 2.66/2.86                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 2.66/2.86                           ( D ) ) =>
% 2.66/2.86                         ( ![F:$i]:
% 2.66/2.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 2.66/2.86                             ( ![G:$i]:
% 2.66/2.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 2.66/2.86                                 ( ( ( ( F ) = ( G ) ) & 
% 2.66/2.86                                     ( r1_tmap_1 @
% 2.66/2.86                                       C @ B @ 
% 2.66/2.86                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 2.66/2.86                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.86    (~( ![A:$i]:
% 2.66/2.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.66/2.86            ( l1_pre_topc @ A ) ) =>
% 2.66/2.86          ( ![B:$i]:
% 2.66/2.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.66/2.86                ( l1_pre_topc @ B ) ) =>
% 2.66/2.86              ( ![C:$i]:
% 2.66/2.86                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.66/2.86                  ( ![D:$i]:
% 2.66/2.86                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.66/2.86                      ( ![E:$i]:
% 2.66/2.86                        ( ( ( v1_funct_1 @ E ) & 
% 2.66/2.86                            ( v1_funct_2 @
% 2.66/2.86                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.66/2.86                            ( m1_subset_1 @
% 2.66/2.86                              E @ 
% 2.66/2.86                              ( k1_zfmisc_1 @
% 2.66/2.86                                ( k2_zfmisc_1 @
% 2.66/2.86                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.66/2.86                          ( ( ( g1_pre_topc @
% 2.66/2.86                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 2.66/2.86                              ( D ) ) =>
% 2.66/2.86                            ( ![F:$i]:
% 2.66/2.86                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 2.66/2.86                                ( ![G:$i]:
% 2.66/2.86                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 2.66/2.86                                    ( ( ( ( F ) = ( G ) ) & 
% 2.66/2.86                                        ( r1_tmap_1 @
% 2.66/2.86                                          C @ B @ 
% 2.66/2.86                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 2.66/2.86                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.66/2.86    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 2.66/2.86  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('1', plain,
% 2.66/2.86      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 2.66/2.86        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('2', plain, (((sk_F) = (sk_G))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('3', plain,
% 2.66/2.86      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 2.66/2.86        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 2.66/2.86      inference('demod', [status(thm)], ['1', '2'])).
% 2.66/2.86  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('5', plain,
% 2.66/2.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 2.66/2.86         = (sk_D))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf(t2_tsep_1, axiom,
% 2.66/2.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 2.66/2.86  thf('6', plain,
% 2.66/2.86      (![X57 : $i]: ((m1_pre_topc @ X57 @ X57) | ~ (l1_pre_topc @ X57))),
% 2.66/2.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.66/2.86  thf(t65_pre_topc, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( l1_pre_topc @ B ) =>
% 2.66/2.86           ( ( m1_pre_topc @ A @ B ) <=>
% 2.66/2.86             ( m1_pre_topc @
% 2.66/2.86               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 2.66/2.86  thf('7', plain,
% 2.66/2.86      (![X41 : $i, X42 : $i]:
% 2.66/2.86         (~ (l1_pre_topc @ X41)
% 2.66/2.86          | ~ (m1_pre_topc @ X42 @ X41)
% 2.66/2.86          | (m1_pre_topc @ X42 @ 
% 2.66/2.86             (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 2.66/2.86          | ~ (l1_pre_topc @ X42))),
% 2.66/2.86      inference('cnf', [status(esa)], [t65_pre_topc])).
% 2.66/2.86  thf('8', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | (m1_pre_topc @ X0 @ 
% 2.66/2.86             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.66/2.86          | ~ (l1_pre_topc @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.66/2.86  thf('9', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((m1_pre_topc @ X0 @ 
% 2.66/2.86           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.66/2.86          | ~ (l1_pre_topc @ X0))),
% 2.66/2.86      inference('simplify', [status(thm)], ['8'])).
% 2.66/2.86  thf('10', plain,
% 2.66/2.86      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['5', '9'])).
% 2.66/2.86  thf('11', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf(dt_m1_pre_topc, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.66/2.86  thf('12', plain,
% 2.66/2.86      (![X34 : $i, X35 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X34 @ X35)
% 2.66/2.86          | (l1_pre_topc @ X34)
% 2.66/2.86          | ~ (l1_pre_topc @ X35))),
% 2.66/2.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.66/2.86  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 2.66/2.86      inference('sup-', [status(thm)], ['11', '12'])).
% 2.66/2.86  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('15', plain, ((l1_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.66/2.86  thf('16', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['10', '15'])).
% 2.66/2.86  thf('17', plain,
% 2.66/2.86      ((m1_subset_1 @ sk_E @ 
% 2.66/2.86        (k1_zfmisc_1 @ 
% 2.66/2.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('18', plain,
% 2.66/2.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 2.66/2.86         = (sk_D))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('19', plain,
% 2.66/2.86      (![X57 : $i]: ((m1_pre_topc @ X57 @ X57) | ~ (l1_pre_topc @ X57))),
% 2.66/2.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.66/2.86  thf(t59_pre_topc, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( m1_pre_topc @
% 2.66/2.86             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 2.66/2.86           ( m1_pre_topc @ B @ A ) ) ) ))).
% 2.66/2.86  thf('20', plain,
% 2.66/2.86      (![X39 : $i, X40 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X39 @ 
% 2.66/2.86             (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)))
% 2.66/2.86          | (m1_pre_topc @ X39 @ X40)
% 2.66/2.86          | ~ (l1_pre_topc @ X40))),
% 2.66/2.86      inference('cnf', [status(esa)], [t59_pre_topc])).
% 2.66/2.86  thf('21', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (l1_pre_topc @ 
% 2.66/2.86             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | (m1_pre_topc @ 
% 2.66/2.86             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['19', '20'])).
% 2.66/2.86  thf('22', plain,
% 2.66/2.86      ((~ (l1_pre_topc @ sk_D)
% 2.66/2.86        | (m1_pre_topc @ 
% 2.66/2.86           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 2.66/2.86           sk_C_1)
% 2.66/2.86        | ~ (l1_pre_topc @ sk_C_1))),
% 2.66/2.86      inference('sup-', [status(thm)], ['18', '21'])).
% 2.66/2.86  thf('23', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('24', plain,
% 2.66/2.86      (![X34 : $i, X35 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X34 @ X35)
% 2.66/2.86          | (l1_pre_topc @ X34)
% 2.66/2.86          | ~ (l1_pre_topc @ X35))),
% 2.66/2.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.66/2.86  thf('25', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['23', '24'])).
% 2.66/2.86  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('27', plain, ((l1_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['25', '26'])).
% 2.66/2.86  thf('28', plain,
% 2.66/2.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 2.66/2.86         = (sk_D))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.66/2.86  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['22', '27', '28', '29'])).
% 2.66/2.86  thf(t35_borsuk_1, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( m1_pre_topc @ B @ A ) =>
% 2.66/2.86           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 2.66/2.86  thf('31', plain,
% 2.66/2.86      (![X58 : $i, X59 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X58 @ X59)
% 2.66/2.86          | (r1_tarski @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X59))
% 2.66/2.86          | ~ (l1_pre_topc @ X59))),
% 2.66/2.86      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 2.66/2.86  thf('32', plain,
% 2.66/2.86      ((~ (l1_pre_topc @ sk_C_1)
% 2.66/2.86        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 2.66/2.86      inference('sup-', [status(thm)], ['30', '31'])).
% 2.66/2.86  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.66/2.86  thf('34', plain,
% 2.66/2.86      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 2.66/2.86      inference('demod', [status(thm)], ['32', '33'])).
% 2.66/2.86  thf(d10_xboole_0, axiom,
% 2.66/2.86    (![A:$i,B:$i]:
% 2.66/2.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.66/2.86  thf('35', plain,
% 2.66/2.86      (![X0 : $i, X2 : $i]:
% 2.66/2.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.66/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.66/2.86  thf('36', plain,
% 2.66/2.86      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 2.66/2.86        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D)))),
% 2.66/2.86      inference('sup-', [status(thm)], ['34', '35'])).
% 2.66/2.86  thf('37', plain,
% 2.66/2.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 2.66/2.86         = (sk_D))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('38', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((m1_pre_topc @ X0 @ 
% 2.66/2.86           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.66/2.86          | ~ (l1_pre_topc @ X0))),
% 2.66/2.86      inference('simplify', [status(thm)], ['8'])).
% 2.66/2.86  thf('39', plain,
% 2.66/2.86      (![X58 : $i, X59 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X58 @ X59)
% 2.66/2.86          | (r1_tarski @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X59))
% 2.66/2.86          | ~ (l1_pre_topc @ X59))),
% 2.66/2.86      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 2.66/2.86  thf('40', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ 
% 2.66/2.86               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 2.66/2.86          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.66/2.86             (u1_struct_0 @ 
% 2.66/2.86              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 2.66/2.86      inference('sup-', [status(thm)], ['38', '39'])).
% 2.66/2.86  thf('41', plain,
% 2.66/2.86      ((~ (l1_pre_topc @ sk_D)
% 2.66/2.86        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86           (u1_struct_0 @ 
% 2.66/2.86            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))))
% 2.66/2.86        | ~ (l1_pre_topc @ sk_C_1))),
% 2.66/2.86      inference('sup-', [status(thm)], ['37', '40'])).
% 2.66/2.86  thf('42', plain, ((l1_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['25', '26'])).
% 2.66/2.86  thf('43', plain,
% 2.66/2.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 2.66/2.86         = (sk_D))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('44', plain, ((l1_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.66/2.86  thf('45', plain,
% 2.66/2.86      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 2.66/2.86  thf('46', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('47', plain,
% 2.66/2.86      ((m1_subset_1 @ sk_E @ 
% 2.66/2.86        (k1_zfmisc_1 @ 
% 2.66/2.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 2.66/2.86      inference('demod', [status(thm)], ['17', '46'])).
% 2.66/2.86  thf('48', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf(d5_tmap_1, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.66/2.86             ( l1_pre_topc @ B ) ) =>
% 2.66/2.86           ( ![C:$i]:
% 2.66/2.86             ( ( m1_pre_topc @ C @ A ) =>
% 2.66/2.86               ( ![D:$i]:
% 2.66/2.86                 ( ( m1_pre_topc @ D @ A ) =>
% 2.66/2.86                   ( ![E:$i]:
% 2.66/2.86                     ( ( ( v1_funct_1 @ E ) & 
% 2.66/2.86                         ( v1_funct_2 @
% 2.66/2.86                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.66/2.86                         ( m1_subset_1 @
% 2.66/2.86                           E @ 
% 2.66/2.86                           ( k1_zfmisc_1 @
% 2.66/2.86                             ( k2_zfmisc_1 @
% 2.66/2.86                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.66/2.86                       ( ( m1_pre_topc @ D @ C ) =>
% 2.66/2.86                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 2.66/2.86                           ( k2_partfun1 @
% 2.66/2.86                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 2.66/2.86                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.66/2.86  thf('49', plain,
% 2.66/2.86      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X47)
% 2.66/2.86          | ~ (v2_pre_topc @ X47)
% 2.66/2.86          | ~ (l1_pre_topc @ X47)
% 2.66/2.86          | ~ (m1_pre_topc @ X48 @ X49)
% 2.66/2.86          | ~ (m1_pre_topc @ X48 @ X50)
% 2.66/2.86          | ((k3_tmap_1 @ X49 @ X47 @ X50 @ X48 @ X51)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X47) @ 
% 2.66/2.86                 X51 @ (u1_struct_0 @ X48)))
% 2.66/2.86          | ~ (m1_subset_1 @ X51 @ 
% 2.66/2.86               (k1_zfmisc_1 @ 
% 2.66/2.86                (k2_zfmisc_1 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X47))))
% 2.66/2.86          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X47))
% 2.66/2.86          | ~ (v1_funct_1 @ X51)
% 2.66/2.86          | ~ (m1_pre_topc @ X50 @ X49)
% 2.66/2.86          | ~ (l1_pre_topc @ X49)
% 2.66/2.86          | ~ (v2_pre_topc @ X49)
% 2.66/2.86          | (v2_struct_0 @ X49))),
% 2.66/2.86      inference('cnf', [status(esa)], [d5_tmap_1])).
% 2.66/2.86  thf('50', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X1 @ 
% 2.66/2.86             (k1_zfmisc_1 @ 
% 2.66/2.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 2.66/2.86          | (v2_struct_0 @ X2)
% 2.66/2.86          | ~ (v2_pre_topc @ X2)
% 2.66/2.86          | ~ (l1_pre_topc @ X2)
% 2.66/2.86          | ~ (m1_pre_topc @ sk_D @ X2)
% 2.66/2.86          | ~ (v1_funct_1 @ X1)
% 2.66/2.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 2.66/2.86          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 2.66/2.86                 X1 @ (u1_struct_0 @ X3)))
% 2.66/2.86          | ~ (m1_pre_topc @ X3 @ sk_D)
% 2.66/2.86          | ~ (m1_pre_topc @ X3 @ X2)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['48', '49'])).
% 2.66/2.86  thf('51', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('52', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('53', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X1 @ 
% 2.66/2.86             (k1_zfmisc_1 @ 
% 2.66/2.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 2.66/2.86          | (v2_struct_0 @ X2)
% 2.66/2.86          | ~ (v2_pre_topc @ X2)
% 2.66/2.86          | ~ (l1_pre_topc @ X2)
% 2.66/2.86          | ~ (m1_pre_topc @ sk_D @ X2)
% 2.66/2.86          | ~ (v1_funct_1 @ X1)
% 2.66/2.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 2.66/2.86          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0) @ 
% 2.66/2.86                 X1 @ (u1_struct_0 @ X3)))
% 2.66/2.86          | ~ (m1_pre_topc @ X3 @ sk_D)
% 2.66/2.86          | ~ (m1_pre_topc @ X3 @ X2)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.66/2.86  thf('54', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (m1_pre_topc @ X1 @ X0)
% 2.66/2.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 2.66/2.86          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X1)))
% 2.66/2.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86               (u1_struct_0 @ sk_B_2))
% 2.66/2.86          | ~ (v1_funct_1 @ sk_E)
% 2.66/2.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['47', '53'])).
% 2.66/2.86  thf('55', plain, ((v2_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('56', plain, ((l1_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('57', plain,
% 2.66/2.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('58', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('59', plain,
% 2.66/2.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['57', '58'])).
% 2.66/2.86  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('61', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | ~ (m1_pre_topc @ X1 @ X0)
% 2.66/2.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 2.66/2.86          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X1)))
% 2.66/2.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('demod', [status(thm)], ['54', '55', '56', '59', '60'])).
% 2.66/2.86  thf('62', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 2.66/2.86          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ sk_C_1)))
% 2.66/2.86          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 2.66/2.86          | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('sup-', [status(thm)], ['16', '61'])).
% 2.66/2.86  thf('63', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['10', '15'])).
% 2.66/2.86  thf('64', plain,
% 2.66/2.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 2.66/2.86         = (sk_D))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('65', plain,
% 2.66/2.86      (![X39 : $i, X40 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X39 @ 
% 2.66/2.86             (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)))
% 2.66/2.86          | (m1_pre_topc @ X39 @ X40)
% 2.66/2.86          | ~ (l1_pre_topc @ X40))),
% 2.66/2.86      inference('cnf', [status(esa)], [t59_pre_topc])).
% 2.66/2.86  thf('66', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X0 @ sk_D)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_C_1)
% 2.66/2.86          | (m1_pre_topc @ X0 @ sk_C_1))),
% 2.66/2.86      inference('sup-', [status(thm)], ['64', '65'])).
% 2.66/2.86  thf('67', plain, ((l1_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.66/2.86  thf('68', plain,
% 2.66/2.86      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C_1))),
% 2.66/2.86      inference('demod', [status(thm)], ['66', '67'])).
% 2.66/2.86  thf('69', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 2.66/2.86      inference('sup-', [status(thm)], ['63', '68'])).
% 2.66/2.86  thf('70', plain,
% 2.66/2.86      ((m1_subset_1 @ sk_E @ 
% 2.66/2.86        (k1_zfmisc_1 @ 
% 2.66/2.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 2.66/2.86      inference('demod', [status(thm)], ['17', '46'])).
% 2.66/2.86  thf(d4_tmap_1, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.66/2.86             ( l1_pre_topc @ B ) ) =>
% 2.66/2.86           ( ![C:$i]:
% 2.66/2.86             ( ( ( v1_funct_1 @ C ) & 
% 2.66/2.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.66/2.86                 ( m1_subset_1 @
% 2.66/2.86                   C @ 
% 2.66/2.86                   ( k1_zfmisc_1 @
% 2.66/2.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.66/2.86               ( ![D:$i]:
% 2.66/2.86                 ( ( m1_pre_topc @ D @ A ) =>
% 2.66/2.86                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 2.66/2.86                     ( k2_partfun1 @
% 2.66/2.86                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.66/2.86                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 2.66/2.86  thf('71', plain,
% 2.66/2.86      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X43)
% 2.66/2.86          | ~ (v2_pre_topc @ X43)
% 2.66/2.86          | ~ (l1_pre_topc @ X43)
% 2.66/2.86          | ~ (m1_pre_topc @ X44 @ X45)
% 2.66/2.86          | ((k2_tmap_1 @ X45 @ X43 @ X46 @ X44)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43) @ 
% 2.66/2.86                 X46 @ (u1_struct_0 @ X44)))
% 2.66/2.86          | ~ (m1_subset_1 @ X46 @ 
% 2.66/2.86               (k1_zfmisc_1 @ 
% 2.66/2.86                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 2.66/2.86          | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 2.66/2.86          | ~ (v1_funct_1 @ X46)
% 2.66/2.86          | ~ (l1_pre_topc @ X45)
% 2.66/2.86          | ~ (v2_pre_topc @ X45)
% 2.66/2.86          | (v2_struct_0 @ X45))),
% 2.66/2.86      inference('cnf', [status(esa)], [d4_tmap_1])).
% 2.66/2.86  thf('72', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_C_1)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_C_1)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_C_1)
% 2.66/2.86          | ~ (v1_funct_1 @ sk_E)
% 2.66/2.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86               (u1_struct_0 @ sk_B_2))
% 2.66/2.86          | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 2.66/2.86          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_B_2)
% 2.66/2.86          | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('sup-', [status(thm)], ['70', '71'])).
% 2.66/2.86  thf('73', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf(cc1_pre_topc, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.66/2.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 2.66/2.86  thf('74', plain,
% 2.66/2.86      (![X5 : $i, X6 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X5 @ X6)
% 2.66/2.86          | (v2_pre_topc @ X5)
% 2.66/2.86          | ~ (l1_pre_topc @ X6)
% 2.66/2.86          | ~ (v2_pre_topc @ X6))),
% 2.66/2.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 2.66/2.86  thf('75', plain,
% 2.66/2.86      ((~ (v2_pre_topc @ sk_A)
% 2.66/2.86        | ~ (l1_pre_topc @ sk_A)
% 2.66/2.86        | (v2_pre_topc @ sk_C_1))),
% 2.66/2.86      inference('sup-', [status(thm)], ['73', '74'])).
% 2.66/2.86  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('78', plain, ((v2_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.66/2.86  thf('79', plain, ((l1_pre_topc @ sk_C_1)),
% 2.66/2.86      inference('demod', [status(thm)], ['13', '14'])).
% 2.66/2.86  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('81', plain,
% 2.66/2.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['57', '58'])).
% 2.66/2.86  thf('82', plain, ((l1_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('83', plain, ((v2_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('84', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_C_1)
% 2.66/2.86          | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 2.66/2.86          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 2.66/2.86          | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)],
% 2.66/2.86                ['72', '78', '79', '80', '81', '82', '83'])).
% 2.66/2.86  thf('85', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_B_2)
% 2.66/2.86        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86               sk_E @ (u1_struct_0 @ sk_C_1)))
% 2.66/2.86        | (v2_struct_0 @ sk_C_1))),
% 2.66/2.86      inference('sup-', [status(thm)], ['69', '84'])).
% 2.66/2.86  thf('86', plain, (~ (v2_struct_0 @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('87', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_C_1)
% 2.66/2.86        | ((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 2.66/2.86      inference('clc', [status(thm)], ['85', '86'])).
% 2.66/2.86  thf('88', plain, (~ (v2_struct_0 @ sk_C_1)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('89', plain,
% 2.66/2.86      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 2.66/2.86      inference('clc', [status(thm)], ['87', '88'])).
% 2.66/2.86  thf('90', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 2.66/2.86          | ((k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 2.66/2.86              = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1))
% 2.66/2.86          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 2.66/2.86          | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['62', '89'])).
% 2.66/2.86  thf('91', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_B_2)
% 2.66/2.86        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 2.66/2.86        | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 2.66/2.86            = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1))
% 2.66/2.86        | ~ (l1_pre_topc @ sk_A)
% 2.66/2.86        | ~ (v2_pre_topc @ sk_A)
% 2.66/2.86        | (v2_struct_0 @ sk_A))),
% 2.66/2.86      inference('sup-', [status(thm)], ['4', '90'])).
% 2.66/2.86  thf('92', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('95', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_B_2)
% 2.66/2.86        | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 2.66/2.86            = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1))
% 2.66/2.86        | (v2_struct_0 @ sk_A))),
% 2.66/2.86      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 2.66/2.86  thf('96', plain, (~ (v2_struct_0 @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('97', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_A)
% 2.66/2.86        | ((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 2.66/2.86            = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)))),
% 2.66/2.86      inference('clc', [status(thm)], ['95', '96'])).
% 2.66/2.86  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('99', plain,
% 2.66/2.86      (((k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E)
% 2.66/2.86         = (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1))),
% 2.66/2.86      inference('clc', [status(thm)], ['97', '98'])).
% 2.66/2.86  thf('100', plain,
% 2.66/2.86      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 2.66/2.86        (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ sk_F)),
% 2.66/2.86      inference('demod', [status(thm)], ['3', '99'])).
% 2.66/2.86  thf('101', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['10', '15'])).
% 2.66/2.86  thf('102', plain,
% 2.66/2.86      ((m1_subset_1 @ sk_E @ 
% 2.66/2.86        (k1_zfmisc_1 @ 
% 2.66/2.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 2.66/2.86      inference('demod', [status(thm)], ['17', '46'])).
% 2.66/2.86  thf('103', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('104', plain,
% 2.66/2.86      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X43)
% 2.66/2.86          | ~ (v2_pre_topc @ X43)
% 2.66/2.86          | ~ (l1_pre_topc @ X43)
% 2.66/2.86          | ~ (m1_pre_topc @ X44 @ X45)
% 2.66/2.86          | ((k2_tmap_1 @ X45 @ X43 @ X46 @ X44)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43) @ 
% 2.66/2.86                 X46 @ (u1_struct_0 @ X44)))
% 2.66/2.86          | ~ (m1_subset_1 @ X46 @ 
% 2.66/2.86               (k1_zfmisc_1 @ 
% 2.66/2.86                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 2.66/2.86          | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 2.66/2.86          | ~ (v1_funct_1 @ X46)
% 2.66/2.86          | ~ (l1_pre_topc @ X45)
% 2.66/2.86          | ~ (v2_pre_topc @ X45)
% 2.66/2.86          | (v2_struct_0 @ X45))),
% 2.66/2.86      inference('cnf', [status(esa)], [d4_tmap_1])).
% 2.66/2.86  thf('105', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X1 @ 
% 2.66/2.86             (k1_zfmisc_1 @ 
% 2.66/2.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_D)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_D)
% 2.66/2.86          | ~ (v1_funct_1 @ X1)
% 2.66/2.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 2.66/2.86          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 2.66/2.86                 X1 @ (u1_struct_0 @ X2)))
% 2.66/2.86          | ~ (m1_pre_topc @ X2 @ sk_D)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['103', '104'])).
% 2.66/2.86  thf('106', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('107', plain,
% 2.66/2.86      (![X5 : $i, X6 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X5 @ X6)
% 2.66/2.86          | (v2_pre_topc @ X5)
% 2.66/2.86          | ~ (l1_pre_topc @ X6)
% 2.66/2.86          | ~ (v2_pre_topc @ X6))),
% 2.66/2.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 2.66/2.86  thf('108', plain,
% 2.66/2.86      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['106', '107'])).
% 2.66/2.86  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('111', plain, ((v2_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['108', '109', '110'])).
% 2.66/2.86  thf('112', plain, ((l1_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['25', '26'])).
% 2.66/2.86  thf('113', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('114', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('115', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X1 @ 
% 2.66/2.86             (k1_zfmisc_1 @ 
% 2.66/2.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | ~ (v1_funct_1 @ X1)
% 2.66/2.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 2.66/2.86          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0) @ 
% 2.66/2.86                 X1 @ (u1_struct_0 @ X2)))
% 2.66/2.86          | ~ (m1_pre_topc @ X2 @ sk_D)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('demod', [status(thm)], ['105', '111', '112', '113', '114'])).
% 2.66/2.86  thf('116', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.66/2.86          | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 2.66/2.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86               (u1_struct_0 @ sk_B_2))
% 2.66/2.86          | ~ (v1_funct_1 @ sk_E)
% 2.66/2.86          | (v2_struct_0 @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['102', '115'])).
% 2.66/2.86  thf('117', plain, ((v2_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('118', plain, ((l1_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('119', plain,
% 2.66/2.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['57', '58'])).
% 2.66/2.86  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('121', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.66/2.86          | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86                 (u1_struct_0 @ sk_B_2) @ sk_E @ (u1_struct_0 @ X0)))
% 2.66/2.86          | (v2_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 2.66/2.86  thf('122', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_D)
% 2.66/2.86        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86               sk_E @ (u1_struct_0 @ sk_C_1)))
% 2.66/2.86        | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('sup-', [status(thm)], ['101', '121'])).
% 2.66/2.86  thf('123', plain, (~ (v2_struct_0 @ sk_D)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('124', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_B_2)
% 2.66/2.86        | ((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86            = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 2.66/2.86      inference('clc', [status(thm)], ['122', '123'])).
% 2.66/2.86  thf('125', plain, (~ (v2_struct_0 @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('126', plain,
% 2.66/2.86      (((k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 2.66/2.86      inference('clc', [status(thm)], ['124', '125'])).
% 2.66/2.86  thf('127', plain,
% 2.66/2.86      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86         = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2) @ 
% 2.66/2.86            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 2.66/2.86      inference('clc', [status(thm)], ['87', '88'])).
% 2.66/2.86  thf('128', plain,
% 2.66/2.86      (((k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1)
% 2.66/2.86         = (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_C_1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['126', '127'])).
% 2.66/2.86  thf('129', plain,
% 2.66/2.86      ((m1_subset_1 @ sk_E @ 
% 2.66/2.86        (k1_zfmisc_1 @ 
% 2.66/2.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 2.66/2.86      inference('demod', [status(thm)], ['17', '46'])).
% 2.66/2.86  thf('130', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf(t67_tmap_1, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.66/2.86             ( l1_pre_topc @ B ) ) =>
% 2.66/2.86           ( ![C:$i]:
% 2.66/2.86             ( ( ( v1_funct_1 @ C ) & 
% 2.66/2.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.66/2.86                 ( m1_subset_1 @
% 2.66/2.86                   C @ 
% 2.66/2.86                   ( k1_zfmisc_1 @
% 2.66/2.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.66/2.86               ( ![D:$i]:
% 2.66/2.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 2.66/2.86                     ( m1_pre_topc @ D @ B ) ) =>
% 2.66/2.86                   ( ![E:$i]:
% 2.66/2.86                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 2.66/2.86                       ( ![F:$i]:
% 2.66/2.86                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 2.66/2.86                           ( ( ( E ) = ( F ) ) =>
% 2.66/2.86                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 2.66/2.86                               ( r1_tmap_1 @
% 2.66/2.86                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.66/2.86  thf('131', plain,
% 2.66/2.86      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X60)
% 2.66/2.86          | ~ (v2_pre_topc @ X60)
% 2.66/2.86          | ~ (l1_pre_topc @ X60)
% 2.66/2.86          | (v2_struct_0 @ X61)
% 2.66/2.86          | ~ (v1_tsep_1 @ X61 @ X60)
% 2.66/2.86          | ~ (m1_pre_topc @ X61 @ X60)
% 2.66/2.86          | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ X61))
% 2.66/2.86          | ~ (r1_tmap_1 @ X61 @ X63 @ (k2_tmap_1 @ X60 @ X63 @ X64 @ X61) @ 
% 2.66/2.86               X62)
% 2.66/2.86          | (r1_tmap_1 @ X60 @ X63 @ X64 @ X65)
% 2.66/2.86          | ((X65) != (X62))
% 2.66/2.86          | ~ (m1_subset_1 @ X65 @ (u1_struct_0 @ X60))
% 2.66/2.86          | ~ (m1_subset_1 @ X64 @ 
% 2.66/2.86               (k1_zfmisc_1 @ 
% 2.66/2.86                (k2_zfmisc_1 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X63))))
% 2.66/2.86          | ~ (v1_funct_2 @ X64 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X63))
% 2.66/2.86          | ~ (v1_funct_1 @ X64)
% 2.66/2.86          | ~ (l1_pre_topc @ X63)
% 2.66/2.86          | ~ (v2_pre_topc @ X63)
% 2.66/2.86          | (v2_struct_0 @ X63))),
% 2.66/2.86      inference('cnf', [status(esa)], [t67_tmap_1])).
% 2.66/2.86  thf('132', plain,
% 2.66/2.86      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 2.66/2.86         ((v2_struct_0 @ X63)
% 2.66/2.86          | ~ (v2_pre_topc @ X63)
% 2.66/2.86          | ~ (l1_pre_topc @ X63)
% 2.66/2.86          | ~ (v1_funct_1 @ X64)
% 2.66/2.86          | ~ (v1_funct_2 @ X64 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X63))
% 2.66/2.86          | ~ (m1_subset_1 @ X64 @ 
% 2.66/2.86               (k1_zfmisc_1 @ 
% 2.66/2.86                (k2_zfmisc_1 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X63))))
% 2.66/2.86          | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ X60))
% 2.66/2.86          | (r1_tmap_1 @ X60 @ X63 @ X64 @ X62)
% 2.66/2.86          | ~ (r1_tmap_1 @ X61 @ X63 @ (k2_tmap_1 @ X60 @ X63 @ X64 @ X61) @ 
% 2.66/2.86               X62)
% 2.66/2.86          | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ X61))
% 2.66/2.86          | ~ (m1_pre_topc @ X61 @ X60)
% 2.66/2.86          | ~ (v1_tsep_1 @ X61 @ X60)
% 2.66/2.86          | (v2_struct_0 @ X61)
% 2.66/2.86          | ~ (l1_pre_topc @ X60)
% 2.66/2.86          | ~ (v2_pre_topc @ X60)
% 2.66/2.86          | (v2_struct_0 @ X60))),
% 2.66/2.86      inference('simplify', [status(thm)], ['131'])).
% 2.66/2.86  thf('133', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X1 @ 
% 2.66/2.86             (k1_zfmisc_1 @ 
% 2.66/2.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_D)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_D)
% 2.66/2.86          | (v2_struct_0 @ X2)
% 2.66/2.86          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 2.66/2.86          | ~ (m1_pre_topc @ X2 @ sk_D)
% 2.66/2.86          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 2.66/2.86          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 2.66/2.86          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 2.66/2.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 2.66/2.86          | ~ (v1_funct_1 @ X1)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['130', '132'])).
% 2.66/2.86  thf('134', plain, ((v2_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['108', '109', '110'])).
% 2.66/2.86  thf('135', plain, ((l1_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['25', '26'])).
% 2.66/2.86  thf('136', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('137', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf('138', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X1 @ 
% 2.66/2.86             (k1_zfmisc_1 @ 
% 2.66/2.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | (v2_struct_0 @ X2)
% 2.66/2.86          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 2.66/2.86          | ~ (m1_pre_topc @ X2 @ sk_D)
% 2.66/2.86          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 2.66/2.86          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 2.66/2.86          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 2.66/2.86          | ~ (v1_funct_1 @ X1)
% 2.66/2.86          | ~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v2_struct_0 @ X0))),
% 2.66/2.86      inference('demod', [status(thm)], ['133', '134', '135', '136', '137'])).
% 2.66/2.86  thf('139', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_B_2)
% 2.66/2.86          | ~ (v1_funct_1 @ sk_E)
% 2.66/2.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 2.66/2.86               (u1_struct_0 @ sk_B_2))
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 2.66/2.86               (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X1) @ X0)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.66/2.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 2.66/2.86          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 2.66/2.86          | (v2_struct_0 @ X1)
% 2.66/2.86          | (v2_struct_0 @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['129', '138'])).
% 2.66/2.86  thf('140', plain, ((v2_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('141', plain, ((l1_pre_topc @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('142', plain, ((v1_funct_1 @ sk_E)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('143', plain,
% 2.66/2.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['57', '58'])).
% 2.66/2.86  thf('144', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 2.66/2.86               (k2_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X1) @ X0)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.66/2.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 2.66/2.86          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 2.66/2.86          | (v2_struct_0 @ X1)
% 2.66/2.86          | (v2_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 2.66/2.86  thf('145', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 2.66/2.86             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ X0)
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | (v2_struct_0 @ sk_C_1)
% 2.66/2.86          | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 2.66/2.86          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('sup-', [status(thm)], ['128', '144'])).
% 2.66/2.86  thf(dt_k2_subset_1, axiom,
% 2.66/2.86    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.66/2.86  thf('146', plain,
% 2.66/2.86      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 2.66/2.86      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.66/2.86  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.66/2.86  thf('147', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 2.66/2.86      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.66/2.86  thf('148', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 2.66/2.86      inference('demod', [status(thm)], ['146', '147'])).
% 2.66/2.86  thf('149', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf(t16_tsep_1, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( m1_pre_topc @ B @ A ) =>
% 2.66/2.86           ( ![C:$i]:
% 2.66/2.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.66/2.86               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 2.66/2.86                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 2.66/2.86                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.66/2.86  thf('150', plain,
% 2.66/2.86      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.66/2.86         (~ (m1_pre_topc @ X52 @ X53)
% 2.66/2.86          | ((X54) != (u1_struct_0 @ X52))
% 2.66/2.86          | ~ (v3_pre_topc @ X54 @ X53)
% 2.66/2.86          | (v1_tsep_1 @ X52 @ X53)
% 2.66/2.86          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 2.66/2.86          | ~ (l1_pre_topc @ X53)
% 2.66/2.86          | ~ (v2_pre_topc @ X53))),
% 2.66/2.86      inference('cnf', [status(esa)], [t16_tsep_1])).
% 2.66/2.86  thf('151', plain,
% 2.66/2.86      (![X52 : $i, X53 : $i]:
% 2.66/2.86         (~ (v2_pre_topc @ X53)
% 2.66/2.86          | ~ (l1_pre_topc @ X53)
% 2.66/2.86          | ~ (m1_subset_1 @ (u1_struct_0 @ X52) @ 
% 2.66/2.86               (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 2.66/2.86          | (v1_tsep_1 @ X52 @ X53)
% 2.66/2.86          | ~ (v3_pre_topc @ (u1_struct_0 @ X52) @ X53)
% 2.66/2.86          | ~ (m1_pre_topc @ X52 @ X53))),
% 2.66/2.86      inference('simplify', [status(thm)], ['150'])).
% 2.66/2.86  thf('152', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.66/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 2.66/2.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.66/2.86          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 2.66/2.86          | (v1_tsep_1 @ X0 @ sk_D)
% 2.66/2.86          | ~ (l1_pre_topc @ sk_D)
% 2.66/2.86          | ~ (v2_pre_topc @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['149', '151'])).
% 2.66/2.86  thf('153', plain, ((l1_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['25', '26'])).
% 2.66/2.86  thf('154', plain, ((v2_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['108', '109', '110'])).
% 2.66/2.86  thf('155', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.66/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 2.66/2.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.66/2.86          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 2.66/2.86          | (v1_tsep_1 @ X0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.66/2.86  thf('156', plain,
% 2.66/2.86      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 2.66/2.86        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 2.66/2.86        | ~ (m1_pre_topc @ sk_C_1 @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['148', '155'])).
% 2.66/2.86  thf('157', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 2.66/2.86      inference('demod', [status(thm)], ['36', '45'])).
% 2.66/2.86  thf(d1_pre_topc, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ( v2_pre_topc @ A ) <=>
% 2.66/2.86         ( ( ![B:$i]:
% 2.66/2.86             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.66/2.86               ( ![C:$i]:
% 2.66/2.86                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.66/2.86                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 2.66/2.86                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 2.66/2.86                     ( r2_hidden @
% 2.66/2.86                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 2.66/2.86                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 2.66/2.86           ( ![B:$i]:
% 2.66/2.86             ( ( m1_subset_1 @
% 2.66/2.86                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.66/2.86               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.66/2.86                 ( r2_hidden @
% 2.66/2.86                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 2.66/2.86                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 2.66/2.86           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 2.66/2.86  thf(zf_stmt_2, axiom,
% 2.66/2.86    (![B:$i,A:$i]:
% 2.66/2.86     ( ( zip_tseitin_5 @ B @ A ) <=>
% 2.66/2.86       ( ( m1_subset_1 @
% 2.66/2.86           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.66/2.86         ( zip_tseitin_4 @ B @ A ) ) ))).
% 2.66/2.86  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 2.66/2.86  thf(zf_stmt_4, axiom,
% 2.66/2.86    (![B:$i,A:$i]:
% 2.66/2.86     ( ( zip_tseitin_4 @ B @ A ) <=>
% 2.66/2.86       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 2.66/2.86         ( r2_hidden @
% 2.66/2.86           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 2.66/2.86  thf(zf_stmt_6, axiom,
% 2.66/2.86    (![B:$i,A:$i]:
% 2.66/2.86     ( ( zip_tseitin_3 @ B @ A ) <=>
% 2.66/2.86       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.66/2.86         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 2.66/2.86  thf(zf_stmt_8, axiom,
% 2.66/2.86    (![C:$i,B:$i,A:$i]:
% 2.66/2.86     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 2.66/2.86       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.66/2.86         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 2.66/2.86  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.66/2.86  thf(zf_stmt_10, axiom,
% 2.66/2.86    (![C:$i,B:$i,A:$i]:
% 2.66/2.86     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 2.66/2.86       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 2.66/2.86         ( r2_hidden @
% 2.66/2.86           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 2.66/2.86  thf(zf_stmt_12, axiom,
% 2.66/2.86    (![C:$i,B:$i,A:$i]:
% 2.66/2.86     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 2.66/2.86       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 2.66/2.86         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_13, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ( v2_pre_topc @ A ) <=>
% 2.66/2.86         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 2.66/2.86           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 2.66/2.86           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 2.66/2.86  thf('158', plain,
% 2.66/2.86      (![X29 : $i]:
% 2.66/2.86         (~ (v2_pre_topc @ X29)
% 2.66/2.86          | (r2_hidden @ (u1_struct_0 @ X29) @ (u1_pre_topc @ X29))
% 2.66/2.86          | ~ (l1_pre_topc @ X29))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_13])).
% 2.66/2.86  thf('159', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 2.66/2.86      inference('demod', [status(thm)], ['146', '147'])).
% 2.66/2.86  thf(d5_pre_topc, axiom,
% 2.66/2.86    (![A:$i]:
% 2.66/2.86     ( ( l1_pre_topc @ A ) =>
% 2.66/2.86       ( ![B:$i]:
% 2.66/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.66/2.86           ( ( v3_pre_topc @ B @ A ) <=>
% 2.66/2.86             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 2.66/2.86  thf('160', plain,
% 2.66/2.86      (![X32 : $i, X33 : $i]:
% 2.66/2.86         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.66/2.86          | ~ (r2_hidden @ X32 @ (u1_pre_topc @ X33))
% 2.66/2.86          | (v3_pre_topc @ X32 @ X33)
% 2.66/2.86          | ~ (l1_pre_topc @ X33))),
% 2.66/2.86      inference('cnf', [status(esa)], [d5_pre_topc])).
% 2.66/2.86  thf('161', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (l1_pre_topc @ X0)
% 2.66/2.86          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.66/2.86          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 2.66/2.86      inference('sup-', [status(thm)], ['159', '160'])).
% 2.66/2.86  thf('162', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (l1_pre_topc @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0))),
% 2.66/2.86      inference('sup-', [status(thm)], ['158', '161'])).
% 2.66/2.86  thf('163', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 2.66/2.86          | ~ (v2_pre_topc @ X0)
% 2.66/2.86          | ~ (l1_pre_topc @ X0))),
% 2.66/2.86      inference('simplify', [status(thm)], ['162'])).
% 2.66/2.86  thf('164', plain,
% 2.66/2.86      (((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 2.66/2.86        | ~ (l1_pre_topc @ sk_D)
% 2.66/2.86        | ~ (v2_pre_topc @ sk_D))),
% 2.66/2.86      inference('sup+', [status(thm)], ['157', '163'])).
% 2.66/2.86  thf('165', plain, ((l1_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['25', '26'])).
% 2.66/2.86  thf('166', plain, ((v2_pre_topc @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['108', '109', '110'])).
% 2.66/2.86  thf('167', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['164', '165', '166'])).
% 2.66/2.86  thf('168', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['10', '15'])).
% 2.66/2.86  thf('169', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['156', '167', '168'])).
% 2.66/2.86  thf('170', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.66/2.86      inference('demod', [status(thm)], ['10', '15'])).
% 2.66/2.86  thf('171', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         (~ (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 2.66/2.86             (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ X0)
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | (v2_struct_0 @ sk_C_1)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['145', '169', '170'])).
% 2.66/2.86  thf('172', plain,
% 2.66/2.86      (![X0 : $i]:
% 2.66/2.86         ((v2_struct_0 @ sk_B_2)
% 2.66/2.86          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X0)
% 2.66/2.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86          | (v2_struct_0 @ sk_C_1)
% 2.66/2.86          | (v2_struct_0 @ sk_D)
% 2.66/2.86          | ~ (r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 2.66/2.86               (k2_tmap_1 @ sk_C_1 @ sk_B_2 @ sk_E @ sk_C_1) @ X0))),
% 2.66/2.86      inference('simplify', [status(thm)], ['171'])).
% 2.66/2.86  thf('173', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_D)
% 2.66/2.86        | (v2_struct_0 @ sk_C_1)
% 2.66/2.86        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 2.66/2.86        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 2.66/2.86        | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('sup-', [status(thm)], ['100', '172'])).
% 2.66/2.86  thf('174', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('175', plain, (((sk_F) = (sk_G))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('176', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 2.66/2.86      inference('demod', [status(thm)], ['174', '175'])).
% 2.66/2.86  thf('177', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_D)
% 2.66/2.86        | (v2_struct_0 @ sk_C_1)
% 2.66/2.86        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 2.66/2.86        | (v2_struct_0 @ sk_B_2))),
% 2.66/2.86      inference('demod', [status(thm)], ['173', '176'])).
% 2.66/2.86  thf('178', plain, (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('179', plain,
% 2.66/2.86      (((v2_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D))),
% 2.66/2.86      inference('sup-', [status(thm)], ['177', '178'])).
% 2.66/2.86  thf('180', plain, (~ (v2_struct_0 @ sk_B_2)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('181', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 2.66/2.86      inference('clc', [status(thm)], ['179', '180'])).
% 2.66/2.86  thf('182', plain, (~ (v2_struct_0 @ sk_D)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('183', plain, ((v2_struct_0 @ sk_C_1)),
% 2.66/2.86      inference('clc', [status(thm)], ['181', '182'])).
% 2.66/2.86  thf('184', plain, ($false), inference('demod', [status(thm)], ['0', '183'])).
% 2.66/2.86  
% 2.66/2.86  % SZS output end Refutation
% 2.66/2.86  
% 2.66/2.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
