%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TearMlBadP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:33 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  178 (2820 expanded)
%              Number of leaves         :   40 ( 830 expanded)
%              Depth                    :   27
%              Number of atoms          : 1472 (65525 expanded)
%              Number of equality atoms :   42 (1775 expanded)
%              Maximal formula depth    :   29 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

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

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('6',plain,(
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

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( m1_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('37',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','44'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('48',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

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

thf('67',plain,(
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

thf('68',plain,(
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
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('72',plain,(
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
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('79',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
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
    inference(demod,[status(thm)],['73','74','81','82','83'])).

thf('85',plain,
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
    inference('sup-',[status(thm)],['3','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

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
    inference(demod,[status(thm)],['21','22'])).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
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
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['87','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('106',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','58'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('107',plain,(
    ! [X16: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('108',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('110',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('111',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('113',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['100','104','105','111','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['10','15'])).

thf('115',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('121',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('124',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','113','114','121','122','123','124','125','126'])).

thf('128',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['0','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TearMlBadP
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:34:18 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.69/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.86  % Solved by: fo/fo7.sh
% 0.69/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.86  % done 501 iterations in 0.425s
% 0.69/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.86  % SZS output start Refutation
% 0.69/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.86  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.69/0.86  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.69/0.86  thf(sk_F_type, type, sk_F: $i).
% 0.69/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.86  thf(sk_E_type, type, sk_E: $i).
% 0.69/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.86  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.69/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.69/0.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.69/0.86  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.69/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.86  thf(sk_G_type, type, sk_G: $i).
% 0.69/0.86  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.69/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.86  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.69/0.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.69/0.86  thf(t88_tmap_1, conjecture,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.86             ( l1_pre_topc @ B ) ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.69/0.86               ( ![D:$i]:
% 0.69/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.69/0.86                   ( ![E:$i]:
% 0.69/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.86                         ( v1_funct_2 @
% 0.69/0.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.86                         ( m1_subset_1 @
% 0.69/0.86                           E @ 
% 0.69/0.86                           ( k1_zfmisc_1 @
% 0.69/0.86                             ( k2_zfmisc_1 @
% 0.69/0.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.86                       ( ( ( g1_pre_topc @
% 0.69/0.86                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.69/0.86                           ( D ) ) =>
% 0.69/0.86                         ( ![F:$i]:
% 0.69/0.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.69/0.86                             ( ![G:$i]:
% 0.69/0.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.69/0.86                                 ( ( ( ( F ) = ( G ) ) & 
% 0.69/0.86                                     ( r1_tmap_1 @
% 0.69/0.86                                       C @ B @ 
% 0.69/0.86                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.69/0.86                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.86    (~( ![A:$i]:
% 0.69/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.69/0.86            ( l1_pre_topc @ A ) ) =>
% 0.69/0.86          ( ![B:$i]:
% 0.69/0.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.86                ( l1_pre_topc @ B ) ) =>
% 0.69/0.86              ( ![C:$i]:
% 0.69/0.86                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.69/0.86                  ( ![D:$i]:
% 0.69/0.86                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.69/0.86                      ( ![E:$i]:
% 0.69/0.86                        ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.86                            ( v1_funct_2 @
% 0.69/0.86                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.86                            ( m1_subset_1 @
% 0.69/0.86                              E @ 
% 0.69/0.86                              ( k1_zfmisc_1 @
% 0.69/0.86                                ( k2_zfmisc_1 @
% 0.69/0.86                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.86                          ( ( ( g1_pre_topc @
% 0.69/0.86                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.69/0.86                              ( D ) ) =>
% 0.69/0.86                            ( ![F:$i]:
% 0.69/0.86                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.69/0.86                                ( ![G:$i]:
% 0.69/0.86                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.69/0.86                                    ( ( ( ( F ) = ( G ) ) & 
% 0.69/0.86                                        ( r1_tmap_1 @
% 0.69/0.86                                          C @ B @ 
% 0.69/0.86                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.69/0.86                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.69/0.86    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.69/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('1', plain,
% 0.69/0.86      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.69/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('2', plain, (((sk_F) = (sk_G))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('3', plain,
% 0.69/0.86      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.69/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('4', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_E @ 
% 0.69/0.86        (k1_zfmisc_1 @ 
% 0.69/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('5', plain,
% 0.69/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t2_tsep_1, axiom,
% 0.69/0.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.69/0.86  thf('6', plain,
% 0.69/0.86      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.69/0.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.69/0.86  thf(t65_pre_topc, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( l1_pre_topc @ B ) =>
% 0.69/0.86           ( ( m1_pre_topc @ A @ B ) <=>
% 0.69/0.86             ( m1_pre_topc @
% 0.69/0.86               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.69/0.86  thf('7', plain,
% 0.69/0.86      (![X14 : $i, X15 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ X14)
% 0.69/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.69/0.86          | (m1_pre_topc @ X15 @ 
% 0.69/0.86             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 0.69/0.86          | ~ (l1_pre_topc @ X15))),
% 0.69/0.86      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.69/0.86  thf('8', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ X0)
% 0.69/0.86          | ~ (l1_pre_topc @ X0)
% 0.69/0.86          | (m1_pre_topc @ X0 @ 
% 0.69/0.86             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.69/0.86          | ~ (l1_pre_topc @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.86  thf('9', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((m1_pre_topc @ X0 @ 
% 0.69/0.86           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.69/0.86          | ~ (l1_pre_topc @ X0))),
% 0.69/0.86      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.86  thf('10', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.69/0.86      inference('sup+', [status(thm)], ['5', '9'])).
% 0.69/0.86  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(dt_m1_pre_topc, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.69/0.86  thf('12', plain,
% 0.69/0.86      (![X10 : $i, X11 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X10 @ X11)
% 0.69/0.86          | (l1_pre_topc @ X10)
% 0.69/0.86          | ~ (l1_pre_topc @ X11))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.69/0.86  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.86  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.69/0.86      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.86  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.69/0.86      inference('demod', [status(thm)], ['10', '15'])).
% 0.69/0.86  thf(t1_tsep_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.69/0.86           ( m1_subset_1 @
% 0.69/0.86             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.69/0.86  thf('17', plain,
% 0.69/0.86      (![X20 : $i, X21 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X20 @ X21)
% 0.69/0.86          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.69/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.69/0.86          | ~ (l1_pre_topc @ X21))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.69/0.86  thf('18', plain,
% 0.69/0.86      ((~ (l1_pre_topc @ sk_D)
% 0.69/0.86        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.86  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('20', plain,
% 0.69/0.86      (![X10 : $i, X11 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X10 @ X11)
% 0.69/0.86          | (l1_pre_topc @ X10)
% 0.69/0.86          | ~ (l1_pre_topc @ X11))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.69/0.86  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.69/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.86  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.86      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.86  thf('24', plain,
% 0.69/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.69/0.86      inference('demod', [status(thm)], ['18', '23'])).
% 0.69/0.86  thf(t3_subset, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.86  thf('25', plain,
% 0.69/0.86      (![X3 : $i, X4 : $i]:
% 0.69/0.86         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.69/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.86  thf('26', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.86  thf(d10_xboole_0, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.86  thf('27', plain,
% 0.69/0.86      (![X0 : $i, X2 : $i]:
% 0.69/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.86  thf('28', plain,
% 0.69/0.86      ((~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.69/0.86        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.86  thf('29', plain,
% 0.69/0.86      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.69/0.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.69/0.86  thf('30', plain,
% 0.69/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t59_pre_topc, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_pre_topc @
% 0.69/0.86             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.69/0.86           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.69/0.86  thf('31', plain,
% 0.69/0.86      (![X12 : $i, X13 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X12 @ 
% 0.69/0.86             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.69/0.86          | (m1_pre_topc @ X12 @ X13)
% 0.69/0.86          | ~ (l1_pre_topc @ X13))),
% 0.69/0.86      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.69/0.86  thf('32', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.86          | ~ (l1_pre_topc @ sk_C)
% 0.69/0.86          | (m1_pre_topc @ X0 @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.86  thf('33', plain, ((l1_pre_topc @ sk_C)),
% 0.69/0.86      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.86  thf('34', plain,
% 0.69/0.86      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['32', '33'])).
% 0.69/0.86  thf('35', plain, ((~ (l1_pre_topc @ sk_D) | (m1_pre_topc @ sk_D @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['29', '34'])).
% 0.69/0.86  thf('36', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.86      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.86  thf('37', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.69/0.86      inference('demod', [status(thm)], ['35', '36'])).
% 0.69/0.86  thf('38', plain,
% 0.69/0.86      (![X20 : $i, X21 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X20 @ X21)
% 0.69/0.86          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.69/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.69/0.86          | ~ (l1_pre_topc @ X21))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.69/0.86  thf('39', plain,
% 0.69/0.86      ((~ (l1_pre_topc @ sk_C)
% 0.69/0.86        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.69/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.86  thf('40', plain, ((l1_pre_topc @ sk_C)),
% 0.69/0.86      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.86  thf('41', plain,
% 0.69/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.69/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.69/0.86      inference('demod', [status(thm)], ['39', '40'])).
% 0.69/0.86  thf('42', plain,
% 0.69/0.86      (![X3 : $i, X4 : $i]:
% 0.69/0.86         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.69/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.86  thf('43', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.86  thf('44', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['28', '43'])).
% 0.69/0.86  thf('45', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_E @ 
% 0.69/0.86        (k1_zfmisc_1 @ 
% 0.69/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '44'])).
% 0.69/0.86  thf(d3_struct_0, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.69/0.86  thf('46', plain,
% 0.69/0.86      (![X8 : $i]:
% 0.69/0.86         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.86  thf('47', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['28', '43'])).
% 0.69/0.86  thf('48', plain,
% 0.69/0.86      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 0.69/0.86      inference('sup+', [status(thm)], ['46', '47'])).
% 0.69/0.86  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.86      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.86  thf(dt_l1_pre_topc, axiom,
% 0.69/0.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.69/0.86  thf('50', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.69/0.86  thf('51', plain, ((l1_struct_0 @ sk_D)),
% 0.69/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.86  thf('52', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['48', '51'])).
% 0.69/0.86  thf('53', plain,
% 0.69/0.86      (![X8 : $i]:
% 0.69/0.86         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.86  thf('54', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['48', '51'])).
% 0.69/0.86  thf('55', plain,
% 0.69/0.86      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.69/0.86      inference('sup+', [status(thm)], ['53', '54'])).
% 0.69/0.86  thf('56', plain, ((l1_pre_topc @ sk_C)),
% 0.69/0.86      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.86  thf('57', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.69/0.86  thf('58', plain, ((l1_struct_0 @ sk_C)),
% 0.69/0.86      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.86  thf('59', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['55', '58'])).
% 0.69/0.86  thf('60', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['52', '59'])).
% 0.69/0.86  thf('61', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_E @ 
% 0.69/0.86        (k1_zfmisc_1 @ 
% 0.69/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.86      inference('demod', [status(thm)], ['45', '60'])).
% 0.69/0.86  thf('62', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['28', '43'])).
% 0.69/0.86  thf('63', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['48', '51'])).
% 0.69/0.86  thf('64', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_D))),
% 0.69/0.86      inference('demod', [status(thm)], ['62', '63'])).
% 0.69/0.86  thf('65', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['55', '58'])).
% 0.69/0.86  thf('66', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['64', '65'])).
% 0.69/0.86  thf(t86_tmap_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.86             ( l1_pre_topc @ B ) ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.69/0.86               ( ![D:$i]:
% 0.69/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.69/0.86                   ( ![E:$i]:
% 0.69/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.86                         ( v1_funct_2 @
% 0.69/0.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.86                         ( m1_subset_1 @
% 0.69/0.86                           E @ 
% 0.69/0.86                           ( k1_zfmisc_1 @
% 0.69/0.86                             ( k2_zfmisc_1 @
% 0.69/0.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.86                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.69/0.86                         ( ![F:$i]:
% 0.69/0.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.69/0.86                             ( ![G:$i]:
% 0.69/0.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.69/0.86                                 ( ( ( F ) = ( G ) ) =>
% 0.69/0.86                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.69/0.86                                     ( r1_tmap_1 @
% 0.69/0.86                                       C @ B @ 
% 0.69/0.86                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('67', plain,
% 0.69/0.86      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X26)
% 0.69/0.86          | ~ (v2_pre_topc @ X26)
% 0.69/0.86          | ~ (l1_pre_topc @ X26)
% 0.69/0.86          | (v2_struct_0 @ X27)
% 0.69/0.86          | ~ (m1_pre_topc @ X27 @ X28)
% 0.69/0.86          | ~ (v1_tsep_1 @ X29 @ X27)
% 0.69/0.86          | ~ (m1_pre_topc @ X29 @ X27)
% 0.69/0.86          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.69/0.86          | ((X30) != (X31))
% 0.69/0.86          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.69/0.86               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.69/0.86          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X30)
% 0.69/0.86          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.69/0.86          | ~ (m1_subset_1 @ X32 @ 
% 0.69/0.86               (k1_zfmisc_1 @ 
% 0.69/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.69/0.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.69/0.86          | ~ (v1_funct_1 @ X32)
% 0.69/0.86          | ~ (m1_pre_topc @ X29 @ X28)
% 0.69/0.86          | (v2_struct_0 @ X29)
% 0.69/0.86          | ~ (l1_pre_topc @ X28)
% 0.69/0.86          | ~ (v2_pre_topc @ X28)
% 0.69/0.86          | (v2_struct_0 @ X28))),
% 0.69/0.86      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.69/0.86  thf('68', plain,
% 0.69/0.86      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X28)
% 0.69/0.86          | ~ (v2_pre_topc @ X28)
% 0.69/0.86          | ~ (l1_pre_topc @ X28)
% 0.69/0.86          | (v2_struct_0 @ X29)
% 0.69/0.86          | ~ (m1_pre_topc @ X29 @ X28)
% 0.69/0.86          | ~ (v1_funct_1 @ X32)
% 0.69/0.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.69/0.86          | ~ (m1_subset_1 @ X32 @ 
% 0.69/0.86               (k1_zfmisc_1 @ 
% 0.69/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.69/0.86          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.69/0.86          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X31)
% 0.69/0.86          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.69/0.86               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.69/0.86          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 0.69/0.86          | ~ (m1_pre_topc @ X29 @ X27)
% 0.69/0.86          | ~ (v1_tsep_1 @ X29 @ X27)
% 0.69/0.86          | ~ (m1_pre_topc @ X27 @ X28)
% 0.69/0.86          | (v2_struct_0 @ X27)
% 0.69/0.86          | ~ (l1_pre_topc @ X26)
% 0.69/0.86          | ~ (v2_pre_topc @ X26)
% 0.69/0.86          | (v2_struct_0 @ X26))),
% 0.69/0.86      inference('simplify', [status(thm)], ['67'])).
% 0.69/0.86  thf('69', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ 
% 0.69/0.86             (k1_zfmisc_1 @ 
% 0.69/0.86              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.69/0.86          | (v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v2_pre_topc @ X0)
% 0.69/0.86          | ~ (l1_pre_topc @ X0)
% 0.69/0.86          | (v2_struct_0 @ sk_D)
% 0.69/0.86          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.69/0.86          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.69/0.86          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.69/0.86          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 0.69/0.86          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.69/0.86               X4)
% 0.69/0.86          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.69/0.86          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.69/0.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.69/0.86          | ~ (v1_funct_1 @ X1)
% 0.69/0.86          | ~ (m1_pre_topc @ X3 @ X2)
% 0.69/0.86          | (v2_struct_0 @ X3)
% 0.69/0.86          | ~ (l1_pre_topc @ X2)
% 0.69/0.86          | ~ (v2_pre_topc @ X2)
% 0.69/0.86          | (v2_struct_0 @ X2))),
% 0.69/0.86      inference('sup-', [status(thm)], ['66', '68'])).
% 0.69/0.86  thf('70', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['64', '65'])).
% 0.69/0.86  thf('71', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['64', '65'])).
% 0.69/0.86  thf('72', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ 
% 0.69/0.86             (k1_zfmisc_1 @ 
% 0.69/0.86              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.69/0.86          | (v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v2_pre_topc @ X0)
% 0.69/0.86          | ~ (l1_pre_topc @ X0)
% 0.69/0.86          | (v2_struct_0 @ sk_D)
% 0.69/0.86          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.69/0.86          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.69/0.86          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.69/0.86          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 0.69/0.86          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.69/0.86               X4)
% 0.69/0.86          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.69/0.86          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.69/0.86          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.69/0.86          | ~ (v1_funct_1 @ X1)
% 0.69/0.86          | ~ (m1_pre_topc @ X3 @ X2)
% 0.69/0.86          | (v2_struct_0 @ X3)
% 0.69/0.86          | ~ (l1_pre_topc @ X2)
% 0.69/0.86          | ~ (v2_pre_topc @ X2)
% 0.69/0.86          | (v2_struct_0 @ X2))),
% 0.69/0.86      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.69/0.86  thf('73', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v2_pre_topc @ X0)
% 0.69/0.86          | ~ (l1_pre_topc @ X0)
% 0.69/0.86          | (v2_struct_0 @ X1)
% 0.69/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.86          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.69/0.86          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.69/0.86          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.69/0.86               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.69/0.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.69/0.86          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.69/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.69/0.86          | (v2_struct_0 @ sk_D)
% 0.69/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.69/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.69/0.86          | (v2_struct_0 @ sk_B))),
% 0.69/0.86      inference('sup-', [status(thm)], ['61', '72'])).
% 0.69/0.86  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('75', plain,
% 0.69/0.86      (![X8 : $i]:
% 0.69/0.86         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.86  thf('76', plain,
% 0.69/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('77', plain,
% 0.69/0.86      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.69/0.86        | ~ (l1_struct_0 @ sk_D))),
% 0.69/0.86      inference('sup+', [status(thm)], ['75', '76'])).
% 0.69/0.86  thf('78', plain, ((l1_struct_0 @ sk_D)),
% 0.69/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.86  thf('79', plain,
% 0.69/0.86      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.69/0.86      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.86  thf('80', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['55', '58'])).
% 0.69/0.86  thf('81', plain,
% 0.69/0.86      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.69/0.86      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.86  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('84', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v2_pre_topc @ X0)
% 0.69/0.86          | ~ (l1_pre_topc @ X0)
% 0.69/0.86          | (v2_struct_0 @ X1)
% 0.69/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.69/0.86          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.69/0.86          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.69/0.86               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.69/0.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.69/0.86          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.69/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.69/0.86          | (v2_struct_0 @ sk_D)
% 0.69/0.86          | (v2_struct_0 @ sk_B))),
% 0.69/0.86      inference('demod', [status(thm)], ['73', '74', '81', '82', '83'])).
% 0.69/0.86  thf('85', plain,
% 0.69/0.86      (((v2_struct_0 @ sk_B)
% 0.69/0.86        | (v2_struct_0 @ sk_D)
% 0.69/0.86        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.69/0.86        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.69/0.86        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.69/0.86        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.69/0.86        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.69/0.86        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.69/0.86        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.69/0.86        | (v2_struct_0 @ sk_C)
% 0.69/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.86        | (v2_struct_0 @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '84'])).
% 0.69/0.86  thf('86', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('87', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['52', '59'])).
% 0.69/0.86  thf('88', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['64', '65'])).
% 0.69/0.86  thf(t16_tsep_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.69/0.86                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.69/0.86                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('89', plain,
% 0.69/0.86      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.86         (~ (m1_pre_topc @ X17 @ X18)
% 0.69/0.86          | ((X19) != (u1_struct_0 @ X17))
% 0.69/0.86          | ~ (v3_pre_topc @ X19 @ X18)
% 0.69/0.86          | (v1_tsep_1 @ X17 @ X18)
% 0.69/0.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.69/0.86          | ~ (l1_pre_topc @ X18)
% 0.69/0.86          | ~ (v2_pre_topc @ X18))),
% 0.69/0.86      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.69/0.86  thf('90', plain,
% 0.69/0.86      (![X17 : $i, X18 : $i]:
% 0.69/0.86         (~ (v2_pre_topc @ X18)
% 0.69/0.86          | ~ (l1_pre_topc @ X18)
% 0.69/0.86          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.69/0.86               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.69/0.86          | (v1_tsep_1 @ X17 @ X18)
% 0.69/0.86          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.69/0.87          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.69/0.87      inference('simplify', [status(thm)], ['89'])).
% 0.69/0.87  thf('91', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.69/0.87             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.69/0.87          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.69/0.87          | (v1_tsep_1 @ X0 @ sk_D)
% 0.69/0.87          | ~ (l1_pre_topc @ sk_D)
% 0.69/0.87          | ~ (v2_pre_topc @ sk_D))),
% 0.69/0.87      inference('sup-', [status(thm)], ['88', '90'])).
% 0.69/0.87  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.87  thf('93', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(cc1_pre_topc, axiom,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.87       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.69/0.87  thf('94', plain,
% 0.69/0.87      (![X6 : $i, X7 : $i]:
% 0.69/0.87         (~ (m1_pre_topc @ X6 @ X7)
% 0.69/0.87          | (v2_pre_topc @ X6)
% 0.69/0.87          | ~ (l1_pre_topc @ X7)
% 0.69/0.87          | ~ (v2_pre_topc @ X7))),
% 0.69/0.87      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.69/0.87  thf('95', plain,
% 0.69/0.87      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.69/0.87      inference('sup-', [status(thm)], ['93', '94'])).
% 0.69/0.87  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('98', plain, ((v2_pre_topc @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.69/0.87  thf('99', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.69/0.87             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.69/0.87          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.87          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.69/0.87          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.69/0.87      inference('demod', [status(thm)], ['91', '92', '98'])).
% 0.69/0.87  thf('100', plain,
% 0.69/0.87      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.69/0.87           (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.69/0.87        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.69/0.87        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.69/0.87        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 0.69/0.87      inference('sup-', [status(thm)], ['87', '99'])).
% 0.69/0.87  thf('101', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.69/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.87  thf('102', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.87      inference('simplify', [status(thm)], ['101'])).
% 0.69/0.87  thf('103', plain,
% 0.69/0.87      (![X3 : $i, X5 : $i]:
% 0.69/0.87         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.87  thf('104', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['102', '103'])).
% 0.69/0.87  thf('105', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.69/0.87      inference('demod', [status(thm)], ['52', '59'])).
% 0.69/0.87  thf('106', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.69/0.87      inference('demod', [status(thm)], ['55', '58'])).
% 0.69/0.87  thf(fc10_tops_1, axiom,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.87       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.69/0.87  thf('107', plain,
% 0.69/0.87      (![X16 : $i]:
% 0.69/0.87         ((v3_pre_topc @ (k2_struct_0 @ X16) @ X16)
% 0.69/0.87          | ~ (l1_pre_topc @ X16)
% 0.69/0.87          | ~ (v2_pre_topc @ X16))),
% 0.69/0.87      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.69/0.87  thf('108', plain,
% 0.69/0.87      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.69/0.87        | ~ (v2_pre_topc @ sk_D)
% 0.69/0.87        | ~ (l1_pre_topc @ sk_D))),
% 0.69/0.87      inference('sup+', [status(thm)], ['106', '107'])).
% 0.69/0.87  thf('109', plain, ((v2_pre_topc @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.69/0.87  thf('110', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.87  thf('111', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.69/0.87  thf('112', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['10', '15'])).
% 0.69/0.87  thf('113', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['100', '104', '105', '111', '112'])).
% 0.69/0.87  thf('114', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.69/0.87      inference('demod', [status(thm)], ['10', '15'])).
% 0.69/0.87  thf('115', plain,
% 0.69/0.87      (![X8 : $i]:
% 0.69/0.87         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.69/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.87  thf('116', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('117', plain, (((sk_F) = (sk_G))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('118', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.69/0.87      inference('demod', [status(thm)], ['116', '117'])).
% 0.69/0.87  thf('119', plain,
% 0.69/0.87      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.69/0.87      inference('sup+', [status(thm)], ['115', '118'])).
% 0.69/0.87  thf('120', plain, ((l1_struct_0 @ sk_C)),
% 0.69/0.87      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.87  thf('121', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.69/0.87      inference('demod', [status(thm)], ['119', '120'])).
% 0.69/0.87  thf('122', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.69/0.87      inference('demod', [status(thm)], ['52', '59'])).
% 0.69/0.87  thf('123', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.69/0.87      inference('demod', [status(thm)], ['119', '120'])).
% 0.69/0.87  thf('124', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('127', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_B)
% 0.69/0.87        | (v2_struct_0 @ sk_D)
% 0.69/0.87        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.69/0.87        | (v2_struct_0 @ sk_C)
% 0.69/0.87        | (v2_struct_0 @ sk_A))),
% 0.69/0.87      inference('demod', [status(thm)],
% 0.69/0.87                ['85', '86', '113', '114', '121', '122', '123', '124', '125', 
% 0.69/0.87                 '126'])).
% 0.69/0.87  thf('128', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('129', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_A)
% 0.69/0.87        | (v2_struct_0 @ sk_C)
% 0.69/0.87        | (v2_struct_0 @ sk_D)
% 0.69/0.87        | (v2_struct_0 @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['127', '128'])).
% 0.69/0.87  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('131', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['129', '130'])).
% 0.69/0.87  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('133', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.69/0.87      inference('clc', [status(thm)], ['131', '132'])).
% 0.69/0.87  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('135', plain, ((v2_struct_0 @ sk_C)),
% 0.69/0.87      inference('clc', [status(thm)], ['133', '134'])).
% 0.69/0.87  thf('136', plain, ($false), inference('demod', [status(thm)], ['0', '135'])).
% 0.69/0.87  
% 0.69/0.87  % SZS output end Refutation
% 0.69/0.87  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
