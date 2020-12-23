%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hYrRVp9baF

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:34 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  152 (1470 expanded)
%              Number of leaves         :   36 ( 445 expanded)
%              Depth                    :   21
%              Number of atoms          : 1514 (41584 expanded)
%              Number of equality atoms :   25 (1095 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['11','16','17','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ( m1_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('38',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_connsp_2 @ ( sk_C @ X18 @ X17 ) @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ sk_D ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ sk_D ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ ( sk_C @ X0 @ sk_D ) @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference('sup-',[status(thm)],['3','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_connsp_2 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_D @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('58',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('59',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_D @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf(t83_tmap_1,axiom,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X32 )
      | ( X32 != X30 )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X32 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('73',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( m1_connsp_2 @ X4 @ sk_D @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( m1_connsp_2 @ X4 @ sk_D @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X3 @ sk_D @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X3 @ sk_D @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('91',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('93',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('95',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('96',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','93','94','95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('102',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference('sup-',[status(thm)],['3','51'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','103','104'])).

thf('106',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hYrRVp9baF
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 168 iterations in 0.101s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.37/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.55  thf(t88_tmap_1, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.55             ( l1_pre_topc @ B ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.55               ( ![D:$i]:
% 0.37/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.55                   ( ![E:$i]:
% 0.37/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.55                         ( v1_funct_2 @
% 0.37/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.55                         ( m1_subset_1 @
% 0.37/0.55                           E @ 
% 0.37/0.55                           ( k1_zfmisc_1 @
% 0.37/0.55                             ( k2_zfmisc_1 @
% 0.37/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.55                       ( ( ( g1_pre_topc @
% 0.37/0.55                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.37/0.55                           ( D ) ) =>
% 0.37/0.55                         ( ![F:$i]:
% 0.37/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.55                             ( ![G:$i]:
% 0.37/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.37/0.55                                 ( ( ( ( F ) = ( G ) ) & 
% 0.37/0.55                                     ( r1_tmap_1 @
% 0.37/0.55                                       C @ B @ 
% 0.37/0.55                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.37/0.55                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.55            ( l1_pre_topc @ A ) ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.55                ( l1_pre_topc @ B ) ) =>
% 0.37/0.55              ( ![C:$i]:
% 0.37/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.55                  ( ![D:$i]:
% 0.37/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.55                      ( ![E:$i]:
% 0.37/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.55                            ( v1_funct_2 @
% 0.37/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.55                            ( m1_subset_1 @
% 0.37/0.55                              E @ 
% 0.37/0.55                              ( k1_zfmisc_1 @
% 0.37/0.55                                ( k2_zfmisc_1 @
% 0.37/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.55                          ( ( ( g1_pre_topc @
% 0.37/0.55                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.37/0.55                              ( D ) ) =>
% 0.37/0.55                            ( ![F:$i]:
% 0.37/0.55                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.55                                ( ![G:$i]:
% 0.37/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.37/0.55                                    ( ( ( ( F ) = ( G ) ) & 
% 0.37/0.55                                        ( r1_tmap_1 @
% 0.37/0.55                                          C @ B @ 
% 0.37/0.55                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.37/0.55                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.37/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('2', plain, (((sk_F) = (sk_G))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.37/0.55         = (sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t2_tsep_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.55  thf(t65_pre_topc, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( l1_pre_topc @ B ) =>
% 0.37/0.55           ( ( m1_pre_topc @ A @ B ) <=>
% 0.37/0.55             ( m1_pre_topc @
% 0.37/0.55               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X12)
% 0.37/0.55          | ~ (m1_pre_topc @ X13 @ X12)
% 0.37/0.55          | (m1_pre_topc @ X13 @ 
% 0.37/0.55             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.37/0.55          | ~ (l1_pre_topc @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X0)
% 0.37/0.55          | ~ (l1_pre_topc @ X0)
% 0.37/0.55          | (m1_pre_topc @ X0 @ 
% 0.37/0.55             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.55          | ~ (l1_pre_topc @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((m1_pre_topc @ X0 @ 
% 0.37/0.55           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.55          | ~ (l1_pre_topc @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.55  thf(t35_borsuk_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.55           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X20 @ X21)
% 0.37/0.55          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.37/0.55          | ~ (l1_pre_topc @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X0)
% 0.37/0.55          | ~ (l1_pre_topc @ 
% 0.37/0.55               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.55          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.37/0.55             (u1_struct_0 @ 
% 0.37/0.55              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_D)
% 0.37/0.55        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.37/0.55           (u1_struct_0 @ 
% 0.37/0.55            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))))
% 0.37/0.55        | ~ (l1_pre_topc @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '10'])).
% 0.37/0.55  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_m1_pre_topc, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.55  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.37/0.55         = (sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('18', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.55  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.55  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('22', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '16', '17', '22'])).
% 0.37/0.55  thf(d10_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i]:
% 0.37/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.37/0.55         = (sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.55  thf(t59_pre_topc, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_pre_topc @
% 0.37/0.55             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.37/0.55           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X10 @ 
% 0.37/0.55             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.37/0.55          | (m1_pre_topc @ X10 @ X11)
% 0.37/0.55          | ~ (l1_pre_topc @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ 
% 0.37/0.55             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.55          | ~ (l1_pre_topc @ X0)
% 0.37/0.55          | (m1_pre_topc @ 
% 0.37/0.55             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_D)
% 0.37/0.55        | (m1_pre_topc @ 
% 0.37/0.55           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 0.37/0.55           sk_C_1)
% 0.37/0.55        | ~ (l1_pre_topc @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '29'])).
% 0.37/0.55  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.37/0.55         = (sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X20 @ X21)
% 0.37/0.55          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.37/0.55          | ~ (l1_pre_topc @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_C_1)
% 0.37/0.55        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf(existence_m1_connsp_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X17)
% 0.37/0.55          | ~ (v2_pre_topc @ X17)
% 0.37/0.55          | (v2_struct_0 @ X17)
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.37/0.55          | (m1_connsp_2 @ (sk_C @ X18 @ X17) @ X17 @ X18))),
% 0.37/0.55      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | (m1_connsp_2 @ (sk_C @ X0 @ sk_D) @ sk_D @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.37/0.55          | ~ (l1_pre_topc @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc1_pre_topc, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X6 @ X7)
% 0.37/0.55          | (v2_pre_topc @ X6)
% 0.37/0.55          | ~ (l1_pre_topc @ X7)
% 0.37/0.55          | ~ (v2_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.55  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('47', plain, ((v2_pre_topc @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.37/0.55  thf('48', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | (m1_connsp_2 @ (sk_C @ X0 @ sk_D) @ sk_D @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['41', '47', '48'])).
% 0.37/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((m1_connsp_2 @ (sk_C @ X0 @ sk_D) @ sk_D @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('52', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '51'])).
% 0.37/0.55  thf('53', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('54', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf(dt_m1_connsp_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.37/0.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X14)
% 0.37/0.55          | ~ (v2_pre_topc @ X14)
% 0.37/0.55          | (v2_struct_0 @ X14)
% 0.37/0.55          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.37/0.55          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.55          | ~ (m1_connsp_2 @ X16 @ X14 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (m1_connsp_2 @ X1 @ sk_D @ X0)
% 0.37/0.55          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.37/0.55          | ~ (l1_pre_topc @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.55  thf('57', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('58', plain, ((v2_pre_topc @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.37/0.55  thf('59', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (m1_connsp_2 @ X1 @ sk_D @ X0)
% 0.37/0.55          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.55          | (v2_struct_0 @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_D)
% 0.37/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.55          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['53', '60'])).
% 0.37/0.55  thf('62', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.37/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.37/0.55      inference('clc', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['52', '63'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('66', plain, (((sk_F) = (sk_G))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.37/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_E @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('69', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_E @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.55  thf('71', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf(t83_tmap_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.55             ( l1_pre_topc @ B ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.55               ( ![D:$i]:
% 0.37/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.55                   ( ![E:$i]:
% 0.37/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.55                         ( v1_funct_2 @
% 0.37/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.55                         ( m1_subset_1 @
% 0.37/0.55                           E @ 
% 0.37/0.55                           ( k1_zfmisc_1 @
% 0.37/0.55                             ( k2_zfmisc_1 @
% 0.37/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.37/0.55                         ( ![F:$i]:
% 0.37/0.55                           ( ( m1_subset_1 @
% 0.37/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.37/0.55                             ( ![G:$i]:
% 0.37/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.55                                 ( ![H:$i]:
% 0.37/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.37/0.55                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.37/0.55                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.37/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.37/0.55                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.37/0.55                                         ( r1_tmap_1 @
% 0.37/0.55                                           C @ B @ 
% 0.37/0.55                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.37/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 0.37/0.55         X32 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X25)
% 0.37/0.55          | ~ (v2_pre_topc @ X25)
% 0.37/0.55          | ~ (l1_pre_topc @ X25)
% 0.37/0.55          | (v2_struct_0 @ X26)
% 0.37/0.55          | ~ (m1_pre_topc @ X26 @ X27)
% 0.37/0.55          | ~ (m1_pre_topc @ X28 @ X26)
% 0.37/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.37/0.55          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.37/0.55               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.37/0.55          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X32)
% 0.37/0.55          | ((X32) != (X30))
% 0.37/0.55          | ~ (m1_connsp_2 @ X29 @ X26 @ X32)
% 0.37/0.55          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.37/0.55          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X26))
% 0.37/0.55          | ~ (m1_subset_1 @ X31 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.37/0.55          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.37/0.55          | ~ (v1_funct_1 @ X31)
% 0.37/0.55          | ~ (m1_pre_topc @ X28 @ X27)
% 0.37/0.55          | (v2_struct_0 @ X28)
% 0.37/0.55          | ~ (l1_pre_topc @ X27)
% 0.37/0.55          | ~ (v2_pre_topc @ X27)
% 0.37/0.55          | (v2_struct_0 @ X27))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X27)
% 0.37/0.55          | ~ (v2_pre_topc @ X27)
% 0.37/0.55          | ~ (l1_pre_topc @ X27)
% 0.37/0.55          | (v2_struct_0 @ X28)
% 0.37/0.55          | ~ (m1_pre_topc @ X28 @ X27)
% 0.37/0.55          | ~ (v1_funct_1 @ X31)
% 0.37/0.55          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.37/0.55          | ~ (m1_subset_1 @ X31 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.37/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.37/0.55          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.37/0.55          | ~ (m1_connsp_2 @ X29 @ X26 @ X30)
% 0.37/0.55          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.37/0.55          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.37/0.55               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.37/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.37/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.55          | ~ (m1_pre_topc @ X28 @ X26)
% 0.37/0.55          | ~ (m1_pre_topc @ X26 @ X27)
% 0.37/0.55          | (v2_struct_0 @ X26)
% 0.37/0.55          | ~ (l1_pre_topc @ X25)
% 0.37/0.55          | ~ (v2_pre_topc @ X25)
% 0.37/0.55          | (v2_struct_0 @ X25))),
% 0.37/0.55      inference('simplify', [status(thm)], ['72'])).
% 0.37/0.55  thf('74', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.37/0.55             (k1_zfmisc_1 @ 
% 0.37/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v2_pre_topc @ X0)
% 0.37/0.55          | ~ (l1_pre_topc @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.37/0.55          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.37/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.37/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.37/0.55          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.37/0.55               X5)
% 0.37/0.55          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.37/0.55          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.37/0.55          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.37/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.37/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.37/0.55          | ~ (v1_funct_1 @ X1)
% 0.37/0.55          | ~ (m1_pre_topc @ X3 @ X2)
% 0.37/0.55          | (v2_struct_0 @ X3)
% 0.37/0.55          | ~ (l1_pre_topc @ X2)
% 0.37/0.55          | ~ (v2_pre_topc @ X2)
% 0.37/0.55          | (v2_struct_0 @ X2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['71', '73'])).
% 0.37/0.55  thf('75', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('76', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('77', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.37/0.55             (k1_zfmisc_1 @ 
% 0.37/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v2_pre_topc @ X0)
% 0.37/0.55          | ~ (l1_pre_topc @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.37/0.55          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.37/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.37/0.55          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.37/0.55               X5)
% 0.37/0.55          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.37/0.55          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.37/0.55          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.37/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.37/0.55          | ~ (v1_funct_1 @ X1)
% 0.37/0.55          | ~ (m1_pre_topc @ X3 @ X2)
% 0.37/0.55          | (v2_struct_0 @ X3)
% 0.37/0.55          | ~ (l1_pre_topc @ X2)
% 0.37/0.55          | ~ (v2_pre_topc @ X2)
% 0.37/0.55          | (v2_struct_0 @ X2))),
% 0.37/0.55      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.37/0.55  thf('79', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v2_pre_topc @ X0)
% 0.37/0.55          | ~ (l1_pre_topc @ X0)
% 0.37/0.55          | (v2_struct_0 @ X1)
% 0.37/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.37/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_B))
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.37/0.55          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.37/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.37/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['70', '78'])).
% 0.37/0.55  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('81', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('82', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '38'])).
% 0.37/0.55  thf('83', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['81', '82'])).
% 0.37/0.55  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X0)
% 0.37/0.55          | ~ (v2_pre_topc @ X0)
% 0.37/0.55          | ~ (l1_pre_topc @ X0)
% 0.37/0.55          | (v2_struct_0 @ X1)
% 0.37/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.37/0.55          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.37/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.37/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.37/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.37/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.37/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | (v2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['79', '80', '83', '84', '85'])).
% 0.37/0.55  thf('87', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_D)
% 0.37/0.55          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.37/0.55          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.55          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.37/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.37/0.55          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.37/0.55          | (v2_struct_0 @ sk_C_1)
% 0.37/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.55          | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['67', '86'])).
% 0.37/0.56  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.37/0.56         = (sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_pre_topc @ X0 @ 
% 0.37/0.56           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['89', '90'])).
% 0.37/0.56  thf('92', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('93', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.56  thf('94', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf('95', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf('96', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ sk_D)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.37/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.37/0.56          | (v2_struct_0 @ sk_C_1)
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)],
% 0.37/0.56                ['87', '88', '93', '94', '95', '96', '97', '98'])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_C_1)
% 0.37/0.56        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.37/0.56        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.37/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['64', '99'])).
% 0.37/0.56  thf('101', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '63'])).
% 0.37/0.56  thf(t3_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.56  thf('102', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.56  thf('103', plain,
% 0.37/0.56      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.56  thf('104', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '51'])).
% 0.37/0.56  thf('105', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_C_1)
% 0.37/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['100', '103', '104'])).
% 0.37/0.56  thf('106', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('107', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_D)
% 0.37/0.56        | (v2_struct_0 @ sk_C_1)
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['105', '106'])).
% 0.37/0.56  thf('108', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('109', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['107', '108'])).
% 0.37/0.56  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('111', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.37/0.56      inference('clc', [status(thm)], ['109', '110'])).
% 0.37/0.56  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('113', plain, ((v2_struct_0 @ sk_C_1)),
% 0.37/0.56      inference('clc', [status(thm)], ['111', '112'])).
% 0.37/0.56  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
