%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8Zkc2PPcs

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:31 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  262 (8127 expanded)
%              Number of leaves         :   44 (2340 expanded)
%              Depth                    :   35
%              Number of atoms          : 2591 (195791 expanded)
%              Number of equality atoms :   85 (5418 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('6',plain,(
    ! [X31: $i] :
      ( ( m1_pre_topc @ X31 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X31: $i] :
      ( ( m1_pre_topc @ X31 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['24','29'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( r1_tarski @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('34',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
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
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( r1_tarski @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('41',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','42'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('46',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('55',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','58'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

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

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( ( k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X22 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('68',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('77',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('79',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('84',plain,(
    ! [X31: $i] :
      ( ( m1_pre_topc @ X31 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','58'])).

thf('86',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('87',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( k2_tmap_1 @ X16 @ X14 @ X17 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X17 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('94',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('95',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('97',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

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
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95','96','102','103'])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('107',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(demod,[status(thm)],['3','122'])).

thf('124',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('125',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','58'])).

thf('126',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('127',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( k2_tmap_1 @ X16 @ X14 @ X17 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X17 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('131',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('136',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('137',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','134','135','136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['125','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('143',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['124','144'])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('153',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','58'])).

thf('155',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

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

thf('156',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( v1_tsep_1 @ X35 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ ( k2_tmap_1 @ X34 @ X37 @ X38 @ X35 ) @ X36 )
      | ( r1_tmap_1 @ X34 @ X37 @ X38 @ X39 )
      | ( X39 != X36 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('157',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ( r1_tmap_1 @ X34 @ X37 @ X38 @ X36 )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ ( k2_tmap_1 @ X34 @ X37 @ X38 @ X35 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_tsep_1 @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('160',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('161',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('162',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['154','163'])).

thf('165',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','169'])).

thf('171',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X31: $i] :
      ( ( m1_pre_topc @ X31 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('173',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['171','175'])).

thf('177',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

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

thf('180',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('181',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['179','181'])).

thf('183',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('184',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['178','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('188',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('189',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('190',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('191',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('193',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('194',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('196',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['186','187','188','194','195'])).

thf('197',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('198',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','196','197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','200'])).

thf('202',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('203',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['202','205'])).

thf('207',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('208',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['201','208'])).

thf('210',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,(
    $false ),
    inference(demod,[status(thm)],['0','215'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8Zkc2PPcs
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 576 iterations in 0.255s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.71  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.50/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.71  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.50/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.50/0.71  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.50/0.71  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.50/0.71  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.50/0.71  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.50/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.71  thf(sk_G_type, type, sk_G: $i).
% 0.50/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.50/0.71  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.50/0.71  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.50/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.50/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(t88_tmap_1, conjecture,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.71             ( l1_pre_topc @ B ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.50/0.71               ( ![D:$i]:
% 0.50/0.71                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.50/0.71                   ( ![E:$i]:
% 0.50/0.71                     ( ( ( v1_funct_1 @ E ) & 
% 0.50/0.71                         ( v1_funct_2 @
% 0.50/0.71                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.71                         ( m1_subset_1 @
% 0.50/0.71                           E @ 
% 0.50/0.71                           ( k1_zfmisc_1 @
% 0.50/0.71                             ( k2_zfmisc_1 @
% 0.50/0.71                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.71                       ( ( ( g1_pre_topc @
% 0.50/0.71                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.50/0.71                           ( D ) ) =>
% 0.50/0.71                         ( ![F:$i]:
% 0.50/0.71                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.50/0.71                             ( ![G:$i]:
% 0.50/0.71                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.50/0.71                                 ( ( ( ( F ) = ( G ) ) & 
% 0.50/0.71                                     ( r1_tmap_1 @
% 0.50/0.71                                       C @ B @ 
% 0.50/0.71                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.50/0.71                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i]:
% 0.50/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.50/0.71            ( l1_pre_topc @ A ) ) =>
% 0.50/0.71          ( ![B:$i]:
% 0.50/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.71                ( l1_pre_topc @ B ) ) =>
% 0.50/0.71              ( ![C:$i]:
% 0.50/0.71                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.50/0.71                  ( ![D:$i]:
% 0.50/0.71                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.50/0.71                      ( ![E:$i]:
% 0.50/0.71                        ( ( ( v1_funct_1 @ E ) & 
% 0.50/0.71                            ( v1_funct_2 @
% 0.50/0.71                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.71                            ( m1_subset_1 @
% 0.50/0.71                              E @ 
% 0.50/0.71                              ( k1_zfmisc_1 @
% 0.50/0.71                                ( k2_zfmisc_1 @
% 0.50/0.71                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.71                          ( ( ( g1_pre_topc @
% 0.50/0.71                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.50/0.71                              ( D ) ) =>
% 0.50/0.71                            ( ![F:$i]:
% 0.50/0.71                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.50/0.71                                ( ![G:$i]:
% 0.50/0.71                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.50/0.71                                    ( ( ( ( F ) = ( G ) ) & 
% 0.50/0.71                                        ( r1_tmap_1 @
% 0.50/0.71                                          C @ B @ 
% 0.50/0.71                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.50/0.71                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.50/0.71  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.50/0.71        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('2', plain, (((sk_F) = (sk_G))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.50/0.71        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.50/0.71      inference('demod', [status(thm)], ['1', '2'])).
% 0.50/0.71  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t2_tsep_1, axiom,
% 0.50/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X31 : $i]: ((m1_pre_topc @ X31 @ X31) | ~ (l1_pre_topc @ X31))),
% 0.50/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.50/0.71  thf(t65_pre_topc, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( l1_pre_topc @ B ) =>
% 0.50/0.71           ( ( m1_pre_topc @ A @ B ) <=>
% 0.50/0.71             ( m1_pre_topc @
% 0.50/0.71               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X11 : $i, X12 : $i]:
% 0.50/0.71         (~ (l1_pre_topc @ X11)
% 0.50/0.71          | ~ (m1_pre_topc @ X12 @ X11)
% 0.50/0.71          | (m1_pre_topc @ X12 @ 
% 0.50/0.71             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.50/0.71          | ~ (l1_pre_topc @ X12))),
% 0.50/0.71      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | (m1_pre_topc @ X0 @ 
% 0.50/0.71             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.71          | ~ (l1_pre_topc @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((m1_pre_topc @ X0 @ 
% 0.50/0.71           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.71          | ~ (l1_pre_topc @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['8'])).
% 0.50/0.71  thf('10', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.50/0.71      inference('sup+', [status(thm)], ['5', '9'])).
% 0.50/0.71  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(dt_m1_pre_topc, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X7 : $i, X8 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.50/0.71  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.50/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.71  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['10', '15'])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_E @ 
% 0.50/0.71        (k1_zfmisc_1 @ 
% 0.50/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (![X31 : $i]: ((m1_pre_topc @ X31 @ X31) | ~ (l1_pre_topc @ X31))),
% 0.50/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t59_pre_topc, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_pre_topc @
% 0.50/0.71             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.50/0.71           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X9 @ 
% 0.50/0.71             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.50/0.71          | (m1_pre_topc @ X9 @ X10)
% 0.50/0.71          | ~ (l1_pre_topc @ X10))),
% 0.50/0.71      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_C)
% 0.50/0.71          | (m1_pre_topc @ X0 @ sk_C))),
% 0.50/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.71  thf('22', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.50/0.71  thf('24', plain, ((~ (l1_pre_topc @ sk_D) | (m1_pre_topc @ sk_D @ sk_C))),
% 0.50/0.71      inference('sup-', [status(thm)], ['18', '23'])).
% 0.50/0.71  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X7 : $i, X8 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.50/0.71  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['24', '29'])).
% 0.50/0.71  thf(t35_borsuk_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_pre_topc @ B @ A ) =>
% 0.50/0.71           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X32 : $i, X33 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X32 @ X33)
% 0.50/0.71          | (r1_tarski @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 0.50/0.71          | ~ (l1_pre_topc @ X33))),
% 0.50/0.71      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_C)
% 0.50/0.71        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.71  thf('33', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('34', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['32', '33'])).
% 0.50/0.71  thf(d10_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      (![X0 : $i, X2 : $i]:
% 0.50/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.50/0.71        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.71  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['10', '15'])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      (![X32 : $i, X33 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X32 @ X33)
% 0.50/0.71          | (r1_tarski @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 0.50/0.71          | ~ (l1_pre_topc @ X33))),
% 0.50/0.71      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_D)
% 0.50/0.71        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.71  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('41', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.71  thf('42', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['36', '41'])).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_E @ 
% 0.50/0.71        (k1_zfmisc_1 @ 
% 0.50/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['17', '42'])).
% 0.50/0.71  thf(d3_struct_0, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (![X5 : $i]:
% 0.50/0.71         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.71  thf('45', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['36', '41'])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.50/0.71      inference('sup+', [status(thm)], ['44', '45'])).
% 0.50/0.71  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf(dt_l1_pre_topc, axiom,
% 0.50/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.50/0.71  thf('48', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.71  thf('49', plain, ((l1_struct_0 @ sk_D)),
% 0.50/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.71  thf('50', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['46', '49'])).
% 0.50/0.71  thf('51', plain,
% 0.50/0.71      (![X5 : $i]:
% 0.50/0.71         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.71  thf('52', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['46', '49'])).
% 0.50/0.71  thf('53', plain,
% 0.50/0.71      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.50/0.71      inference('sup+', [status(thm)], ['51', '52'])).
% 0.50/0.71  thf('54', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('55', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.71  thf('56', plain, ((l1_struct_0 @ sk_C)),
% 0.50/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.71  thf('57', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['53', '56'])).
% 0.50/0.71  thf('58', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('59', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_E @ 
% 0.50/0.71        (k1_zfmisc_1 @ 
% 0.50/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['43', '58'])).
% 0.50/0.71  thf('60', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['36', '41'])).
% 0.50/0.71  thf('61', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['46', '49'])).
% 0.50/0.71  thf('62', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['60', '61'])).
% 0.50/0.71  thf('63', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['53', '56'])).
% 0.50/0.71  thf('64', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf(d5_tmap_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.71             ( l1_pre_topc @ B ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( m1_pre_topc @ C @ A ) =>
% 0.50/0.71               ( ![D:$i]:
% 0.50/0.71                 ( ( m1_pre_topc @ D @ A ) =>
% 0.50/0.71                   ( ![E:$i]:
% 0.50/0.71                     ( ( ( v1_funct_1 @ E ) & 
% 0.50/0.71                         ( v1_funct_2 @
% 0.50/0.71                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.71                         ( m1_subset_1 @
% 0.50/0.71                           E @ 
% 0.50/0.71                           ( k1_zfmisc_1 @
% 0.50/0.71                             ( k2_zfmisc_1 @
% 0.50/0.71                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.71                       ( ( m1_pre_topc @ D @ C ) =>
% 0.50/0.71                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.50/0.71                           ( k2_partfun1 @
% 0.50/0.71                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.50/0.71                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('65', plain,
% 0.50/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X18)
% 0.50/0.71          | ~ (v2_pre_topc @ X18)
% 0.50/0.71          | ~ (l1_pre_topc @ X18)
% 0.50/0.71          | ~ (m1_pre_topc @ X19 @ X20)
% 0.50/0.71          | ~ (m1_pre_topc @ X19 @ X21)
% 0.50/0.71          | ((k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.50/0.71                 X22 @ (u1_struct_0 @ X19)))
% 0.50/0.71          | ~ (m1_subset_1 @ X22 @ 
% 0.50/0.71               (k1_zfmisc_1 @ 
% 0.50/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))))
% 0.50/0.71          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))
% 0.50/0.71          | ~ (v1_funct_1 @ X22)
% 0.50/0.71          | ~ (m1_pre_topc @ X21 @ X20)
% 0.50/0.71          | ~ (l1_pre_topc @ X20)
% 0.50/0.71          | ~ (v2_pre_topc @ X20)
% 0.50/0.71          | (v2_struct_0 @ X20))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.50/0.71  thf('66', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.50/0.71          | (v2_struct_0 @ X2)
% 0.50/0.71          | ~ (v2_pre_topc @ X2)
% 0.50/0.71          | ~ (l1_pre_topc @ X2)
% 0.50/0.71          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.50/0.71          | ~ (v1_funct_1 @ X1)
% 0.50/0.71          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.50/0.71          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 0.50/0.71                 X1 @ (u1_struct_0 @ X3)))
% 0.50/0.71          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.50/0.71          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['64', '65'])).
% 0.50/0.71  thf('67', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('68', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('69', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.50/0.71          | (v2_struct_0 @ X2)
% 0.50/0.71          | ~ (v2_pre_topc @ X2)
% 0.50/0.71          | ~ (l1_pre_topc @ X2)
% 0.50/0.71          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.50/0.71          | ~ (v1_funct_1 @ X1)
% 0.50/0.71          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.50/0.71          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.50/0.71                 X1 @ (u1_struct_0 @ X3)))
% 0.50/0.71          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.50/0.71          | ~ (m1_pre_topc @ X3 @ X2)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.50/0.71  thf('70', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.71          | ~ (m1_pre_topc @ X1 @ X0)
% 0.50/0.71          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.50/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ X1)))
% 0.50/0.71          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.50/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.50/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['59', '69'])).
% 0.50/0.71  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('73', plain,
% 0.50/0.71      (![X5 : $i]:
% 0.50/0.71         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.71  thf('74', plain,
% 0.50/0.71      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('75', plain,
% 0.50/0.71      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.50/0.71        | ~ (l1_struct_0 @ sk_D))),
% 0.50/0.71      inference('sup+', [status(thm)], ['73', '74'])).
% 0.50/0.71  thf('76', plain, ((l1_struct_0 @ sk_D)),
% 0.50/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.71  thf('77', plain,
% 0.50/0.71      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['75', '76'])).
% 0.50/0.71  thf('78', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['53', '56'])).
% 0.50/0.71  thf('79', plain,
% 0.50/0.71      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.50/0.71  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('81', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (m1_pre_topc @ X1 @ X0)
% 0.50/0.71          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.50/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ X1)))
% 0.50/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['70', '71', '72', '79', '80'])).
% 0.50/0.71  thf('82', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.50/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ sk_C)))
% 0.50/0.71          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.50/0.71          | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['16', '81'])).
% 0.50/0.71  thf('83', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('84', plain,
% 0.50/0.71      (![X31 : $i]: ((m1_pre_topc @ X31 @ X31) | ~ (l1_pre_topc @ X31))),
% 0.50/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.50/0.71  thf('85', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_E @ 
% 0.50/0.71        (k1_zfmisc_1 @ 
% 0.50/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['43', '58'])).
% 0.50/0.71  thf('86', plain,
% 0.50/0.71      (![X5 : $i]:
% 0.50/0.71         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.71  thf(d4_tmap_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.71             ( l1_pre_topc @ B ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.71                 ( m1_subset_1 @
% 0.50/0.71                   C @ 
% 0.50/0.71                   ( k1_zfmisc_1 @
% 0.50/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.71               ( ![D:$i]:
% 0.50/0.71                 ( ( m1_pre_topc @ D @ A ) =>
% 0.50/0.71                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.50/0.71                     ( k2_partfun1 @
% 0.50/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.50/0.71                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('87', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X14)
% 0.50/0.71          | ~ (v2_pre_topc @ X14)
% 0.50/0.71          | ~ (l1_pre_topc @ X14)
% 0.50/0.71          | ~ (m1_pre_topc @ X15 @ X16)
% 0.50/0.71          | ((k2_tmap_1 @ X16 @ X14 @ X17 @ X15)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14) @ 
% 0.50/0.71                 X17 @ (u1_struct_0 @ X15)))
% 0.50/0.71          | ~ (m1_subset_1 @ X17 @ 
% 0.50/0.71               (k1_zfmisc_1 @ 
% 0.50/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))))
% 0.50/0.71          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))
% 0.50/0.71          | ~ (v1_funct_1 @ X17)
% 0.50/0.71          | ~ (l1_pre_topc @ X16)
% 0.50/0.71          | ~ (v2_pre_topc @ X16)
% 0.50/0.71          | (v2_struct_0 @ X16))),
% 0.50/0.71      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.50/0.71  thf('88', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X2 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.50/0.71          | ~ (l1_struct_0 @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v1_funct_1 @ X2)
% 0.50/0.71          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.50/0.71          | ((k2_tmap_1 @ X0 @ X1 @ X2 @ X3)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 0.50/0.71                 (u1_struct_0 @ X3)))
% 0.50/0.71          | ~ (m1_pre_topc @ X3 @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X1)
% 0.50/0.71          | ~ (v2_pre_topc @ X1)
% 0.50/0.71          | (v2_struct_0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['86', '87'])).
% 0.50/0.71  thf('89', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.71          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.50/0.71          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ X0)))
% 0.50/0.71          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.50/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_C)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_C)
% 0.50/0.71          | (v2_struct_0 @ sk_C)
% 0.50/0.71          | ~ (l1_struct_0 @ sk_C))),
% 0.50/0.71      inference('sup-', [status(thm)], ['85', '88'])).
% 0.50/0.71  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('92', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('93', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('94', plain,
% 0.50/0.71      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.50/0.71  thf('95', plain, ((v1_funct_1 @ sk_E)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('96', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(cc1_pre_topc, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.50/0.71  thf('98', plain,
% 0.50/0.71      (![X3 : $i, X4 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X3 @ X4)
% 0.50/0.71          | (v2_pre_topc @ X3)
% 0.50/0.71          | ~ (l1_pre_topc @ X4)
% 0.50/0.71          | ~ (v2_pre_topc @ X4))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.50/0.71  thf('99', plain,
% 0.50/0.71      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.50/0.71      inference('sup-', [status(thm)], ['97', '98'])).
% 0.50/0.71  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('102', plain, ((v2_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.50/0.71  thf('103', plain, ((l1_struct_0 @ sk_C)),
% 0.50/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.71  thf('104', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.50/0.71          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ X0)))
% 0.50/0.71          | (v2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)],
% 0.50/0.71                ['89', '90', '91', '92', '93', '94', '95', '96', '102', '103'])).
% 0.50/0.71  thf('105', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_C)
% 0.50/0.71        | (v2_struct_0 @ sk_C)
% 0.50/0.71        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.50/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71               sk_E @ (u1_struct_0 @ sk_C)))
% 0.50/0.71        | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['84', '104'])).
% 0.50/0.71  thf('106', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('107', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('108', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_C)
% 0.50/0.71        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.50/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71               sk_E @ (k2_struct_0 @ sk_C)))
% 0.50/0.71        | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.50/0.71  thf('109', plain, (~ (v2_struct_0 @ sk_C)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('110', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_B)
% 0.50/0.71        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.50/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.50/0.71      inference('clc', [status(thm)], ['108', '109'])).
% 0.50/0.71  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('112', plain,
% 0.50/0.71      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.50/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.50/0.71            (k2_struct_0 @ sk_C)))),
% 0.50/0.71      inference('clc', [status(thm)], ['110', '111'])).
% 0.50/0.71  thf('113', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.50/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.50/0.71              = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.50/0.71          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.50/0.71          | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['82', '83', '112'])).
% 0.50/0.71  thf('114', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_B)
% 0.50/0.71        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.50/0.71        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.50/0.71            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.50/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.50/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.71        | (v2_struct_0 @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['4', '113'])).
% 0.50/0.71  thf('115', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('118', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_B)
% 0.50/0.71        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.50/0.71            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.50/0.71        | (v2_struct_0 @ sk_A))),
% 0.50/0.71      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.50/0.71  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('120', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_A)
% 0.50/0.71        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.50/0.71            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)))),
% 0.50/0.71      inference('clc', [status(thm)], ['118', '119'])).
% 0.50/0.71  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('122', plain,
% 0.50/0.71      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.50/0.71         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 0.50/0.71      inference('clc', [status(thm)], ['120', '121'])).
% 0.50/0.71  thf('123', plain,
% 0.50/0.71      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 0.50/0.71        sk_F)),
% 0.50/0.71      inference('demod', [status(thm)], ['3', '122'])).
% 0.50/0.71  thf('124', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['10', '15'])).
% 0.50/0.71  thf('125', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_E @ 
% 0.50/0.71        (k1_zfmisc_1 @ 
% 0.50/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['43', '58'])).
% 0.50/0.71  thf('126', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('127', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X14)
% 0.50/0.71          | ~ (v2_pre_topc @ X14)
% 0.50/0.71          | ~ (l1_pre_topc @ X14)
% 0.50/0.71          | ~ (m1_pre_topc @ X15 @ X16)
% 0.50/0.71          | ((k2_tmap_1 @ X16 @ X14 @ X17 @ X15)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14) @ 
% 0.50/0.71                 X17 @ (u1_struct_0 @ X15)))
% 0.50/0.71          | ~ (m1_subset_1 @ X17 @ 
% 0.50/0.71               (k1_zfmisc_1 @ 
% 0.50/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))))
% 0.50/0.71          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))
% 0.50/0.71          | ~ (v1_funct_1 @ X17)
% 0.50/0.71          | ~ (l1_pre_topc @ X16)
% 0.50/0.71          | ~ (v2_pre_topc @ X16)
% 0.50/0.71          | (v2_struct_0 @ X16))),
% 0.50/0.71      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.50/0.71  thf('128', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_D)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_D)
% 0.50/0.71          | ~ (v1_funct_1 @ X1)
% 0.50/0.71          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.50/0.71          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 0.50/0.71              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 0.50/0.71                 X1 @ (u1_struct_0 @ X2)))
% 0.50/0.71          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['126', '127'])).
% 0.50/0.71  thf('129', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('130', plain,
% 0.50/0.71      (![X3 : $i, X4 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X3 @ X4)
% 0.50/0.71          | (v2_pre_topc @ X3)
% 0.50/0.71          | ~ (l1_pre_topc @ X4)
% 0.50/0.71          | ~ (v2_pre_topc @ X4))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.50/0.71  thf('131', plain,
% 0.50/0.71      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['129', '130'])).
% 0.50/0.71  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('134', plain, ((v2_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.50/0.71  thf('135', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('136', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('137', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('138', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | ~ (v1_funct_1 @ X1)
% 0.50/0.71          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.50/0.71          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.50/0.71                 X1 @ (u1_struct_0 @ X2)))
% 0.50/0.71          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['128', '134', '135', '136', '137'])).
% 0.50/0.71  thf('139', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.71          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.50/0.71          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ X0)))
% 0.50/0.71          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.50/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.50/0.71          | (v2_struct_0 @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['125', '138'])).
% 0.50/0.71  thf('140', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('141', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('142', plain,
% 0.50/0.71      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.50/0.71  thf('143', plain, ((v1_funct_1 @ sk_E)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('144', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.50/0.71          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71                 sk_E @ (u1_struct_0 @ X0)))
% 0.50/0.71          | (v2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 0.50/0.71  thf('145', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_D)
% 0.50/0.71        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.50/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71               sk_E @ (u1_struct_0 @ sk_C)))
% 0.50/0.71        | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['124', '144'])).
% 0.50/0.71  thf('146', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('147', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_D)
% 0.50/0.71        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.50/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71               sk_E @ (k2_struct_0 @ sk_C)))
% 0.50/0.71        | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['145', '146'])).
% 0.50/0.71  thf('148', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('149', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_B)
% 0.50/0.71        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.50/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.71               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.50/0.71      inference('clc', [status(thm)], ['147', '148'])).
% 0.50/0.71  thf('150', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('151', plain,
% 0.50/0.71      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.50/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.50/0.71            (k2_struct_0 @ sk_C)))),
% 0.50/0.71      inference('clc', [status(thm)], ['149', '150'])).
% 0.50/0.71  thf('152', plain,
% 0.50/0.71      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.50/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.50/0.71            (k2_struct_0 @ sk_C)))),
% 0.50/0.71      inference('clc', [status(thm)], ['110', '111'])).
% 0.50/0.71  thf('153', plain,
% 0.50/0.71      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.50/0.71         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.50/0.71      inference('sup+', [status(thm)], ['151', '152'])).
% 0.50/0.71  thf('154', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_E @ 
% 0.50/0.71        (k1_zfmisc_1 @ 
% 0.50/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.71      inference('demod', [status(thm)], ['43', '58'])).
% 0.50/0.71  thf('155', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf(t67_tmap_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.71             ( l1_pre_topc @ B ) ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.50/0.71                 ( m1_subset_1 @
% 0.50/0.71                   C @ 
% 0.50/0.71                   ( k1_zfmisc_1 @
% 0.50/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.50/0.71               ( ![D:$i]:
% 0.50/0.71                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.50/0.71                     ( m1_pre_topc @ D @ B ) ) =>
% 0.50/0.71                   ( ![E:$i]:
% 0.50/0.71                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.50/0.71                       ( ![F:$i]:
% 0.50/0.71                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.50/0.71                           ( ( ( E ) = ( F ) ) =>
% 0.50/0.71                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.50/0.71                               ( r1_tmap_1 @
% 0.50/0.71                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('156', plain,
% 0.50/0.71      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X34)
% 0.50/0.71          | ~ (v2_pre_topc @ X34)
% 0.50/0.71          | ~ (l1_pre_topc @ X34)
% 0.50/0.71          | (v2_struct_0 @ X35)
% 0.50/0.71          | ~ (v1_tsep_1 @ X35 @ X34)
% 0.50/0.71          | ~ (m1_pre_topc @ X35 @ X34)
% 0.50/0.71          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 0.50/0.71          | ~ (r1_tmap_1 @ X35 @ X37 @ (k2_tmap_1 @ X34 @ X37 @ X38 @ X35) @ 
% 0.50/0.71               X36)
% 0.50/0.71          | (r1_tmap_1 @ X34 @ X37 @ X38 @ X39)
% 0.50/0.71          | ((X39) != (X36))
% 0.50/0.71          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X34))
% 0.50/0.71          | ~ (m1_subset_1 @ X38 @ 
% 0.50/0.71               (k1_zfmisc_1 @ 
% 0.50/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))))
% 0.50/0.71          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))
% 0.50/0.71          | ~ (v1_funct_1 @ X38)
% 0.50/0.71          | ~ (l1_pre_topc @ X37)
% 0.50/0.71          | ~ (v2_pre_topc @ X37)
% 0.50/0.71          | (v2_struct_0 @ X37))),
% 0.50/0.71      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.50/0.71  thf('157', plain,
% 0.50/0.71      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.50/0.71         ((v2_struct_0 @ X37)
% 0.50/0.71          | ~ (v2_pre_topc @ X37)
% 0.50/0.71          | ~ (l1_pre_topc @ X37)
% 0.50/0.71          | ~ (v1_funct_1 @ X38)
% 0.50/0.71          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))
% 0.50/0.71          | ~ (m1_subset_1 @ X38 @ 
% 0.50/0.71               (k1_zfmisc_1 @ 
% 0.50/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))))
% 0.50/0.71          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.50/0.71          | (r1_tmap_1 @ X34 @ X37 @ X38 @ X36)
% 0.50/0.71          | ~ (r1_tmap_1 @ X35 @ X37 @ (k2_tmap_1 @ X34 @ X37 @ X38 @ X35) @ 
% 0.50/0.71               X36)
% 0.50/0.71          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 0.50/0.71          | ~ (m1_pre_topc @ X35 @ X34)
% 0.50/0.71          | ~ (v1_tsep_1 @ X35 @ X34)
% 0.50/0.71          | (v2_struct_0 @ X35)
% 0.50/0.71          | ~ (l1_pre_topc @ X34)
% 0.50/0.71          | ~ (v2_pre_topc @ X34)
% 0.50/0.71          | (v2_struct_0 @ X34))),
% 0.50/0.71      inference('simplify', [status(thm)], ['156'])).
% 0.50/0.71  thf('158', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_D)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_D)
% 0.50/0.71          | (v2_struct_0 @ X2)
% 0.50/0.71          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 0.50/0.71          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.50/0.71          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.50/0.71          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 0.50/0.71          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.50/0.71          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.50/0.71          | ~ (v1_funct_1 @ X1)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['155', '157'])).
% 0.50/0.71  thf('159', plain, ((v2_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.50/0.71  thf('160', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('161', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('162', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('163', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.50/0.71             (k1_zfmisc_1 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | (v2_struct_0 @ X2)
% 0.50/0.71          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 0.50/0.71          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.50/0.71          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.50/0.71          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 0.50/0.71          | ~ (m1_subset_1 @ X3 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.50/0.71          | ~ (v1_funct_1 @ X1)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (v2_pre_topc @ X0)
% 0.50/0.71          | (v2_struct_0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['158', '159', '160', '161', '162'])).
% 0.50/0.71  thf('164', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.50/0.71          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 0.50/0.71               X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.50/0.71          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.50/0.71          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | (v2_struct_0 @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['154', '163'])).
% 0.50/0.71  thf('165', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('166', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('167', plain, ((v1_funct_1 @ sk_E)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('168', plain,
% 0.50/0.71      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.50/0.71  thf('169', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 0.50/0.71               X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.50/0.71          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.50/0.71          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.50/0.71          | (v2_struct_0 @ X1)
% 0.50/0.71          | (v2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 0.50/0.71  thf('170', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.50/0.71             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | (v2_struct_0 @ sk_C)
% 0.50/0.71          | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.50/0.71          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['153', '169'])).
% 0.50/0.71  thf('171', plain,
% 0.50/0.71      (![X5 : $i]:
% 0.50/0.71         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.71  thf('172', plain,
% 0.50/0.71      (![X31 : $i]: ((m1_pre_topc @ X31 @ X31) | ~ (l1_pre_topc @ X31))),
% 0.50/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.50/0.71  thf(t1_tsep_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_pre_topc @ B @ A ) =>
% 0.50/0.71           ( m1_subset_1 @
% 0.50/0.71             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.50/0.71  thf('173', plain,
% 0.50/0.71      (![X29 : $i, X30 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X29 @ X30)
% 0.50/0.71          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.50/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.50/0.71          | ~ (l1_pre_topc @ X30))),
% 0.50/0.71      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.50/0.71  thf('174', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (l1_pre_topc @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0)
% 0.50/0.71          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['172', '173'])).
% 0.50/0.71  thf('175', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.71           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.50/0.71          | ~ (l1_pre_topc @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['174'])).
% 0.50/0.71  thf('176', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.71           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.50/0.71          | ~ (l1_struct_0 @ X0)
% 0.50/0.71          | ~ (l1_pre_topc @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['171', '175'])).
% 0.50/0.71  thf('177', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.71  thf('178', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (l1_pre_topc @ X0)
% 0.50/0.71          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.71             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.50/0.71      inference('clc', [status(thm)], ['176', '177'])).
% 0.50/0.71  thf('179', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf(t16_tsep_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_pre_topc @ B @ A ) =>
% 0.50/0.71           ( ![C:$i]:
% 0.50/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.50/0.71                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.50/0.71                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.50/0.71  thf('180', plain,
% 0.50/0.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.50/0.71         (~ (m1_pre_topc @ X23 @ X24)
% 0.50/0.71          | ((X25) != (u1_struct_0 @ X23))
% 0.50/0.71          | ~ (v3_pre_topc @ X25 @ X24)
% 0.50/0.71          | (v1_tsep_1 @ X23 @ X24)
% 0.50/0.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.50/0.71          | ~ (l1_pre_topc @ X24)
% 0.50/0.71          | ~ (v2_pre_topc @ X24))),
% 0.50/0.71      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.50/0.71  thf('181', plain,
% 0.50/0.71      (![X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (v2_pre_topc @ X24)
% 0.50/0.71          | ~ (l1_pre_topc @ X24)
% 0.50/0.71          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.50/0.71               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.50/0.71          | (v1_tsep_1 @ X23 @ X24)
% 0.50/0.71          | ~ (v3_pre_topc @ (u1_struct_0 @ X23) @ X24)
% 0.50/0.71          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.50/0.71      inference('simplify', [status(thm)], ['180'])).
% 0.50/0.71  thf('182', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.71             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.50/0.71          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.50/0.71          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.50/0.71          | (v1_tsep_1 @ X0 @ sk_D)
% 0.50/0.71          | ~ (l1_pre_topc @ sk_D)
% 0.50/0.71          | ~ (v2_pre_topc @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['179', '181'])).
% 0.50/0.71  thf('183', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('184', plain, ((v2_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.50/0.71  thf('185', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.71             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.50/0.71          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.50/0.71          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.50/0.71          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['182', '183', '184'])).
% 0.50/0.71  thf('186', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_C)
% 0.50/0.71        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.50/0.71        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.50/0.71        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['178', '185'])).
% 0.50/0.71  thf('187', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('188', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('189', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['53', '56'])).
% 0.50/0.71  thf(fc10_tops_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.50/0.71  thf('190', plain,
% 0.50/0.71      (![X13 : $i]:
% 0.50/0.71         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.50/0.71          | ~ (l1_pre_topc @ X13)
% 0.50/0.71          | ~ (v2_pre_topc @ X13))),
% 0.50/0.71      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.50/0.71  thf('191', plain,
% 0.50/0.71      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.50/0.71        | ~ (v2_pre_topc @ sk_D)
% 0.50/0.71        | ~ (l1_pre_topc @ sk_D))),
% 0.50/0.71      inference('sup+', [status(thm)], ['189', '190'])).
% 0.50/0.71  thf('192', plain, ((v2_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.50/0.71  thf('193', plain, ((l1_pre_topc @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('194', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.50/0.71  thf('195', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['10', '15'])).
% 0.50/0.71  thf('196', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['186', '187', '188', '194', '195'])).
% 0.50/0.71  thf('197', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.50/0.71      inference('demod', [status(thm)], ['10', '15'])).
% 0.50/0.71  thf('198', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['50', '57'])).
% 0.50/0.71  thf('199', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.50/0.71             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | (v2_struct_0 @ sk_C)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['170', '196', '197', '198'])).
% 0.50/0.71  thf('200', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((v2_struct_0 @ sk_B)
% 0.50/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.50/0.71          | (v2_struct_0 @ sk_C)
% 0.50/0.71          | (v2_struct_0 @ sk_D)
% 0.50/0.71          | ~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.50/0.71               (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['199'])).
% 0.50/0.71  thf('201', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_D)
% 0.50/0.71        | (v2_struct_0 @ sk_C)
% 0.50/0.71        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.50/0.71        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.50/0.71        | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['123', '200'])).
% 0.50/0.71  thf('202', plain,
% 0.50/0.71      (![X5 : $i]:
% 0.50/0.71         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.71  thf('203', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('204', plain, (((sk_F) = (sk_G))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('205', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['203', '204'])).
% 0.50/0.71  thf('206', plain,
% 0.50/0.71      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.50/0.71      inference('sup+', [status(thm)], ['202', '205'])).
% 0.50/0.71  thf('207', plain, ((l1_struct_0 @ sk_C)),
% 0.50/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.50/0.71  thf('208', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['206', '207'])).
% 0.50/0.71  thf('209', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_D)
% 0.50/0.71        | (v2_struct_0 @ sk_C)
% 0.50/0.71        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.50/0.71        | (v2_struct_0 @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['201', '208'])).
% 0.50/0.71  thf('210', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('211', plain,
% 0.50/0.71      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['209', '210'])).
% 0.50/0.71  thf('212', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('213', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.50/0.71      inference('clc', [status(thm)], ['211', '212'])).
% 0.50/0.71  thf('214', plain, (~ (v2_struct_0 @ sk_D)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('215', plain, ((v2_struct_0 @ sk_C)),
% 0.50/0.71      inference('clc', [status(thm)], ['213', '214'])).
% 0.50/0.71  thf('216', plain, ($false), inference('demod', [status(thm)], ['0', '215'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
