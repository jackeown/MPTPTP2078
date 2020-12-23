%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eLLnZDMdjf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:20 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 599 expanded)
%              Number of leaves         :   39 ( 183 expanded)
%              Depth                    :   29
%              Number of atoms          : 2193 (21153 expanded)
%              Number of equality atoms :   13 ( 275 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t86_tmap_1,conjecture,(
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
                       => ( ( ( v1_tsep_1 @ C @ D )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tmap_1])).

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

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_connsp_2 @ ( sk_C @ X17 @ X16 ) @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['17','18'])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_connsp_2 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_C_1 @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('25',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_C_1 @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_F @ ( sk_C @ sk_F @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('37',plain,
    ( ( r2_hidden @ sk_F @ ( sk_C @ sk_F @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_F @ ( sk_C @ sk_F @ sk_C_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('60',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X30 @ X33 )
      | ~ ( r1_tmap_1 @ X33 @ X29 @ X34 @ X32 )
      | ( X32 != X35 )
      | ( r1_tmap_1 @ X30 @ X29 @ ( k3_tmap_1 @ X31 @ X29 @ X33 @ X30 @ X34 ) @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X30 @ X29 @ ( k3_tmap_1 @ X31 @ X29 @ X33 @ X30 @ X34 ) @ X35 )
      | ~ ( r1_tmap_1 @ X33 @ X29 @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X30 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['56'])).

thf('82',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('94',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['57','92','93'])).

thf('95',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['55','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tmap_1,axiom,(
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
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_tmap_1 @ X39 @ X36 @ ( k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42 ) @ X41 )
      | ( r1_tmap_1 @ X37 @ X36 @ X42 @ X43 )
      | ( X43 != X41 )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r2_hidden @ X43 @ X40 )
      | ~ ( v3_pre_topc @ X40 @ X37 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('98',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X37 ) )
      | ~ ( v3_pre_topc @ X40 @ X37 )
      | ~ ( r2_hidden @ X41 @ X40 )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X39 ) )
      | ( r1_tmap_1 @ X37 @ X36 @ X42 @ X41 )
      | ~ ( r1_tmap_1 @ X39 @ X36 @ ( k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_pre_topc @ X39 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('111',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','113'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','50'])).

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

thf('118',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( X23
       != ( u1_struct_0 @ X21 ) )
      | ~ ( v1_tsep_1 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('119',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X21 ) @ X22 )
      | ~ ( v1_tsep_1 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('124',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('126',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['120','121','122','123','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','116','130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','131'])).

thf('133',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['56'])).

thf('134',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['57','92'])).

thf('135',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('138',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['0','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eLLnZDMdjf
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:32:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 147 iterations in 0.081s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.56  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(t86_tmap_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.56             ( l1_pre_topc @ B ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56               ( ![D:$i]:
% 0.38/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.56                   ( ![E:$i]:
% 0.38/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56                         ( v1_funct_2 @
% 0.38/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.56                         ( m1_subset_1 @
% 0.38/0.56                           E @ 
% 0.38/0.56                           ( k1_zfmisc_1 @
% 0.38/0.56                             ( k2_zfmisc_1 @
% 0.38/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.56                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.38/0.56                         ( ![F:$i]:
% 0.38/0.56                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.56                             ( ![G:$i]:
% 0.38/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.56                                 ( ( ( F ) = ( G ) ) =>
% 0.38/0.56                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.38/0.56                                     ( r1_tmap_1 @
% 0.38/0.56                                       C @ B @ 
% 0.38/0.56                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56            ( l1_pre_topc @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.56                ( l1_pre_topc @ B ) ) =>
% 0.38/0.56              ( ![C:$i]:
% 0.38/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56                  ( ![D:$i]:
% 0.38/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.56                      ( ![E:$i]:
% 0.38/0.56                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56                            ( v1_funct_2 @
% 0.38/0.56                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.56                            ( m1_subset_1 @
% 0.38/0.56                              E @ 
% 0.38/0.56                              ( k1_zfmisc_1 @
% 0.38/0.56                                ( k2_zfmisc_1 @
% 0.38/0.56                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.56                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.38/0.56                            ( ![F:$i]:
% 0.38/0.56                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.56                                ( ![G:$i]:
% 0.38/0.56                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.56                                    ( ( ( F ) = ( G ) ) =>
% 0.38/0.56                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.38/0.56                                        ( r1_tmap_1 @
% 0.38/0.56                                          C @ B @ 
% 0.38/0.56                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.38/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('2', plain, (((sk_F) = (sk_G))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf(existence_m1_connsp_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X16)
% 0.38/0.56          | ~ (v2_pre_topc @ X16)
% 0.38/0.56          | (v2_struct_0 @ X16)
% 0.38/0.56          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.38/0.56          | (m1_connsp_2 @ (sk_C @ X17 @ X16) @ X16 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.38/0.56        | (v2_struct_0 @ sk_C_1)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X9 @ X10)
% 0.38/0.56          | (v2_pre_topc @ X9)
% 0.38/0.56          | ~ (l1_pre_topc @ X10)
% 0.38/0.56          | ~ (v2_pre_topc @ X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (v2_pre_topc @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('11', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.56  thf('12', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_m1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.38/0.56          | (l1_pre_topc @ X11)
% 0.38/0.56          | ~ (l1_pre_topc @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.56  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('16', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.38/0.56        | (v2_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.38/0.56  thf('18', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('19', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.38/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.38/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('21', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf(dt_m1_connsp_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.38/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X13)
% 0.38/0.56          | ~ (v2_pre_topc @ X13)
% 0.38/0.56          | (v2_struct_0 @ X13)
% 0.38/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.38/0.56          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.56          | ~ (m1_connsp_2 @ X15 @ X13 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F)
% 0.38/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56          | (v2_struct_0 @ sk_C_1)
% 0.38/0.56          | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.56  thf('25', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F)
% 0.38/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56          | (v2_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.38/0.56  thf('27', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56          | ~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F))),
% 0.38/0.56      inference('clc', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '28'])).
% 0.38/0.56  thf(t6_connsp_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.56          | ~ (m1_connsp_2 @ X18 @ X19 @ X20)
% 0.38/0.56          | (r2_hidden @ X20 @ X18)
% 0.38/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.38/0.56          | ~ (l1_pre_topc @ X19)
% 0.38/0.56          | ~ (v2_pre_topc @ X19)
% 0.38/0.56          | (v2_struct_0 @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_C_1)
% 0.38/0.56          | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_C_1)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56          | (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1))
% 0.38/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.56  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_C_1)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56          | (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1))
% 0.38/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (((r2_hidden @ sk_F @ (sk_C @ sk_F @ sk_C_1))
% 0.38/0.56        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56        | (v2_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '34'])).
% 0.38/0.56  thf('36', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (((r2_hidden @ sk_F @ (sk_C @ sk_F @ sk_C_1)) | (v2_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('39', plain, ((r2_hidden @ sk_F @ (sk_C @ sk_F @ sk_C_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('40', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf(d2_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X3 @ X4)
% 0.38/0.56          | (r2_hidden @ X3 @ X4)
% 0.38/0.56          | (v1_xboole_0 @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.56  thf('43', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t1_tsep_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.56           ( m1_subset_1 @
% 0.38/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X24 @ X25)
% 0.38/0.56          | (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.38/0.56          | ~ (l1_pre_topc @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_D)
% 0.38/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.38/0.56          | (l1_pre_topc @ X11)
% 0.38/0.56          | ~ (l1_pre_topc @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.56  thf('48', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.56  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.38/0.56      inference('demod', [status(thm)], ['45', '50'])).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.38/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.56      inference('split', [status(esa)], ['52'])).
% 0.38/0.56  thf('54', plain, (((sk_F) = (sk_G))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.38/0.56        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.38/0.56       ~
% 0.38/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.38/0.56      inference('split', [status(esa)], ['56'])).
% 0.38/0.56  thf('58', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('59', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('split', [status(esa)], ['52'])).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_E @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t81_tmap_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.56             ( l1_pre_topc @ B ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56               ( ![D:$i]:
% 0.38/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.56                   ( ![E:$i]:
% 0.38/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56                         ( v1_funct_2 @
% 0.38/0.56                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.56                         ( m1_subset_1 @
% 0.38/0.56                           E @ 
% 0.38/0.56                           ( k1_zfmisc_1 @
% 0.38/0.56                             ( k2_zfmisc_1 @
% 0.38/0.56                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.56                       ( ![F:$i]:
% 0.38/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.56                           ( ![G:$i]:
% 0.38/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.56                               ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.56                                   ( m1_pre_topc @ D @ C ) & 
% 0.38/0.56                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.38/0.56                                 ( r1_tmap_1 @
% 0.38/0.56                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.38/0.56                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         ((v2_struct_0 @ X29)
% 0.38/0.56          | ~ (v2_pre_topc @ X29)
% 0.38/0.56          | ~ (l1_pre_topc @ X29)
% 0.38/0.56          | (v2_struct_0 @ X30)
% 0.38/0.56          | ~ (m1_pre_topc @ X30 @ X31)
% 0.38/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 0.38/0.56          | ~ (m1_pre_topc @ X30 @ X33)
% 0.38/0.56          | ~ (r1_tmap_1 @ X33 @ X29 @ X34 @ X32)
% 0.38/0.56          | ((X32) != (X35))
% 0.38/0.56          | (r1_tmap_1 @ X30 @ X29 @ 
% 0.38/0.56             (k3_tmap_1 @ X31 @ X29 @ X33 @ X30 @ X34) @ X35)
% 0.38/0.56          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X30))
% 0.38/0.56          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.56               (k1_zfmisc_1 @ 
% 0.38/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29))))
% 0.38/0.56          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29))
% 0.38/0.56          | ~ (v1_funct_1 @ X34)
% 0.38/0.56          | ~ (m1_pre_topc @ X33 @ X31)
% 0.38/0.56          | (v2_struct_0 @ X33)
% 0.38/0.56          | ~ (l1_pre_topc @ X31)
% 0.38/0.56          | ~ (v2_pre_topc @ X31)
% 0.38/0.56          | (v2_struct_0 @ X31))),
% 0.38/0.56      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         ((v2_struct_0 @ X31)
% 0.38/0.56          | ~ (v2_pre_topc @ X31)
% 0.38/0.56          | ~ (l1_pre_topc @ X31)
% 0.38/0.56          | (v2_struct_0 @ X33)
% 0.38/0.56          | ~ (m1_pre_topc @ X33 @ X31)
% 0.38/0.56          | ~ (v1_funct_1 @ X34)
% 0.38/0.56          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29))
% 0.38/0.56          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.56               (k1_zfmisc_1 @ 
% 0.38/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29))))
% 0.38/0.56          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X30))
% 0.38/0.56          | (r1_tmap_1 @ X30 @ X29 @ 
% 0.38/0.56             (k3_tmap_1 @ X31 @ X29 @ X33 @ X30 @ X34) @ X35)
% 0.38/0.56          | ~ (r1_tmap_1 @ X33 @ X29 @ X34 @ X35)
% 0.38/0.56          | ~ (m1_pre_topc @ X30 @ X33)
% 0.38/0.56          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.38/0.56          | ~ (m1_pre_topc @ X30 @ X31)
% 0.38/0.56          | (v2_struct_0 @ X30)
% 0.38/0.56          | ~ (l1_pre_topc @ X29)
% 0.38/0.56          | ~ (v2_pre_topc @ X29)
% 0.38/0.56          | (v2_struct_0 @ X29))),
% 0.38/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_B)
% 0.38/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.38/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.38/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.38/0.56          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.38/0.56             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | ~ (l1_pre_topc @ X1)
% 0.38/0.56          | ~ (v2_pre_topc @ X1)
% 0.38/0.56          | (v2_struct_0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['61', '63'])).
% 0.38/0.56  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_B)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.38/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.38/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.38/0.56          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.38/0.56             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | ~ (l1_pre_topc @ X1)
% 0.38/0.56          | ~ (v2_pre_topc @ X1)
% 0.38/0.56          | (v2_struct_0 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      ((![X0 : $i, X1 : $i]:
% 0.38/0.56          ((v2_struct_0 @ X0)
% 0.38/0.56           | ~ (v2_pre_topc @ X0)
% 0.38/0.56           | ~ (l1_pre_topc @ X0)
% 0.38/0.56           | (v2_struct_0 @ sk_D)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.38/0.56           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.38/0.56           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.38/0.56           | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.56           | (v2_struct_0 @ X1)
% 0.38/0.56           | (v2_struct_0 @ sk_B)))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['60', '69'])).
% 0.38/0.56  thf('71', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      ((![X0 : $i, X1 : $i]:
% 0.38/0.56          ((v2_struct_0 @ X0)
% 0.38/0.56           | ~ (v2_pre_topc @ X0)
% 0.38/0.56           | ~ (l1_pre_topc @ X0)
% 0.38/0.56           | (v2_struct_0 @ sk_D)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.38/0.56           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.38/0.56           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.56           | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.56           | (v2_struct_0 @ X1)
% 0.38/0.56           | (v2_struct_0 @ sk_B)))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((v2_struct_0 @ sk_B)
% 0.38/0.56           | (v2_struct_0 @ sk_C_1)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.38/0.56           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.56           | (v2_struct_0 @ sk_D)
% 0.38/0.56           | ~ (l1_pre_topc @ X0)
% 0.38/0.56           | ~ (v2_pre_topc @ X0)
% 0.38/0.56           | (v2_struct_0 @ X0)))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['59', '72'])).
% 0.38/0.56  thf('74', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((v2_struct_0 @ sk_B)
% 0.38/0.56           | (v2_struct_0 @ sk_C_1)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.38/0.56           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.56           | (v2_struct_0 @ sk_D)
% 0.38/0.56           | ~ (l1_pre_topc @ X0)
% 0.38/0.56           | ~ (v2_pre_topc @ X0)
% 0.38/0.56           | (v2_struct_0 @ X0)))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      ((((v2_struct_0 @ sk_A)
% 0.38/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56         | (v2_struct_0 @ sk_D)
% 0.38/0.56         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.56         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.56         | (v2_struct_0 @ sk_C_1)
% 0.38/0.56         | (v2_struct_0 @ sk_B)))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['58', '75'])).
% 0.38/0.56  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      ((((v2_struct_0 @ sk_A)
% 0.38/0.56         | (v2_struct_0 @ sk_D)
% 0.38/0.56         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.56         | (v2_struct_0 @ sk_C_1)
% 0.38/0.56         | (v2_struct_0 @ sk_B)))
% 0.38/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.56      inference('split', [status(esa)], ['56'])).
% 0.38/0.56  thf('82', plain, (((sk_F) = (sk_G))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      ((((v2_struct_0 @ sk_B)
% 0.38/0.56         | (v2_struct_0 @ sk_C_1)
% 0.38/0.56         | (v2_struct_0 @ sk_D)
% 0.38/0.56         | (v2_struct_0 @ sk_A)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['80', '83'])).
% 0.38/0.56  thf('85', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('86', plain,
% 0.38/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.56  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('clc', [status(thm)], ['86', '87'])).
% 0.38/0.56  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_C_1))
% 0.38/0.56         <= (~
% 0.38/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('clc', [status(thm)], ['88', '89'])).
% 0.38/0.56  thf('91', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.38/0.56       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.38/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.38/0.56       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.38/0.56      inference('split', [status(esa)], ['52'])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['57', '92', '93'])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['55', '94'])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_E @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t84_tmap_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.56             ( l1_pre_topc @ B ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56               ( ![D:$i]:
% 0.38/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.56                   ( ![E:$i]:
% 0.38/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.56                         ( v1_funct_2 @
% 0.38/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.56                         ( m1_subset_1 @
% 0.38/0.56                           E @ 
% 0.38/0.56                           ( k1_zfmisc_1 @
% 0.38/0.56                             ( k2_zfmisc_1 @
% 0.38/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.56                       ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.56                         ( ![F:$i]:
% 0.38/0.56                           ( ( m1_subset_1 @
% 0.38/0.56                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.38/0.56                             ( ![G:$i]:
% 0.38/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.56                                 ( ![H:$i]:
% 0.38/0.56                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.56                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.38/0.56                                         ( r2_hidden @ G @ F ) & 
% 0.38/0.56                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.38/0.56                                         ( ( G ) = ( H ) ) ) =>
% 0.38/0.56                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.38/0.56                                         ( r1_tmap_1 @
% 0.38/0.56                                           C @ B @ 
% 0.38/0.56                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.38/0.56                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 0.38/0.56         X43 : $i]:
% 0.38/0.56         ((v2_struct_0 @ X36)
% 0.38/0.56          | ~ (v2_pre_topc @ X36)
% 0.38/0.56          | ~ (l1_pre_topc @ X36)
% 0.38/0.56          | (v2_struct_0 @ X37)
% 0.38/0.56          | ~ (m1_pre_topc @ X37 @ X38)
% 0.38/0.56          | ~ (m1_pre_topc @ X39 @ X37)
% 0.38/0.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.38/0.56          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 0.38/0.56          | ~ (r1_tmap_1 @ X39 @ X36 @ 
% 0.38/0.56               (k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42) @ X41)
% 0.38/0.56          | (r1_tmap_1 @ X37 @ X36 @ X42 @ X43)
% 0.38/0.56          | ((X43) != (X41))
% 0.38/0.56          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X39))
% 0.38/0.56          | ~ (r2_hidden @ X43 @ X40)
% 0.38/0.56          | ~ (v3_pre_topc @ X40 @ X37)
% 0.38/0.56          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X37))
% 0.38/0.56          | ~ (m1_subset_1 @ X42 @ 
% 0.38/0.56               (k1_zfmisc_1 @ 
% 0.38/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))))
% 0.38/0.56          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))
% 0.38/0.56          | ~ (v1_funct_1 @ X42)
% 0.38/0.56          | ~ (m1_pre_topc @ X39 @ X38)
% 0.38/0.56          | (v2_struct_0 @ X39)
% 0.38/0.56          | ~ (l1_pre_topc @ X38)
% 0.38/0.56          | ~ (v2_pre_topc @ X38)
% 0.38/0.56          | (v2_struct_0 @ X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.56         ((v2_struct_0 @ X38)
% 0.38/0.56          | ~ (v2_pre_topc @ X38)
% 0.38/0.56          | ~ (l1_pre_topc @ X38)
% 0.38/0.56          | (v2_struct_0 @ X39)
% 0.38/0.56          | ~ (m1_pre_topc @ X39 @ X38)
% 0.38/0.56          | ~ (v1_funct_1 @ X42)
% 0.38/0.56          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))
% 0.38/0.56          | ~ (m1_subset_1 @ X42 @ 
% 0.38/0.56               (k1_zfmisc_1 @ 
% 0.38/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))))
% 0.38/0.56          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 0.38/0.56          | ~ (v3_pre_topc @ X40 @ X37)
% 0.38/0.56          | ~ (r2_hidden @ X41 @ X40)
% 0.38/0.56          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X39))
% 0.38/0.56          | (r1_tmap_1 @ X37 @ X36 @ X42 @ X41)
% 0.38/0.56          | ~ (r1_tmap_1 @ X39 @ X36 @ 
% 0.38/0.56               (k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42) @ X41)
% 0.38/0.56          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 0.38/0.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.38/0.56          | ~ (m1_pre_topc @ X39 @ X37)
% 0.38/0.56          | ~ (m1_pre_topc @ X37 @ X38)
% 0.38/0.56          | (v2_struct_0 @ X37)
% 0.38/0.56          | ~ (l1_pre_topc @ X36)
% 0.38/0.56          | ~ (v2_pre_topc @ X36)
% 0.38/0.56          | (v2_struct_0 @ X36))),
% 0.38/0.56      inference('simplify', [status(thm)], ['97'])).
% 0.38/0.56  thf('99', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_B)
% 0.38/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.38/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.38/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.56          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.56          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.38/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.38/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.56          | (v2_struct_0 @ X1)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['96', '98'])).
% 0.38/0.56  thf('100', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('101', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('103', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_B)
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.38/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.38/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.56          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.56          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.38/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.38/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.56          | (v2_struct_0 @ X1)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.38/0.56  thf('105', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_A)
% 0.38/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56          | (v2_struct_0 @ sk_C_1)
% 0.38/0.56          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.38/0.56          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.38/0.56          | ~ (r2_hidden @ sk_F @ X0)
% 0.38/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.56          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.38/0.56          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | (v2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '104'])).
% 0.38/0.56  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('108', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('109', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('110', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('111', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('112', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('113', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_A)
% 0.38/0.56          | (v2_struct_0 @ sk_C_1)
% 0.38/0.56          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.38/0.56          | ~ (r2_hidden @ sk_F @ X0)
% 0.38/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | (v2_struct_0 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)],
% 0.38/0.56                ['105', '106', '107', '108', '109', '110', '111', '112'])).
% 0.38/0.56  thf('114', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_B)
% 0.38/0.56        | (v2_struct_0 @ sk_D)
% 0.38/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.56        | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 0.38/0.56        | (v2_struct_0 @ sk_C_1)
% 0.38/0.56        | (v2_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['51', '113'])).
% 0.38/0.56  thf(d10_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('115', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.56  thf('116', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.56      inference('simplify', [status(thm)], ['115'])).
% 0.38/0.56  thf('117', plain,
% 0.38/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.38/0.56      inference('demod', [status(thm)], ['45', '50'])).
% 0.38/0.56  thf(t16_tsep_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.56                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.38/0.56                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('118', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X21 @ X22)
% 0.38/0.56          | ((X23) != (u1_struct_0 @ X21))
% 0.38/0.56          | ~ (v1_tsep_1 @ X21 @ X22)
% 0.38/0.56          | ~ (m1_pre_topc @ X21 @ X22)
% 0.38/0.56          | (v3_pre_topc @ X23 @ X22)
% 0.38/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.56          | ~ (l1_pre_topc @ X22)
% 0.38/0.56          | ~ (v2_pre_topc @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.38/0.56  thf('119', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i]:
% 0.38/0.56         (~ (v2_pre_topc @ X22)
% 0.38/0.56          | ~ (l1_pre_topc @ X22)
% 0.38/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.38/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.56          | (v3_pre_topc @ (u1_struct_0 @ X21) @ X22)
% 0.38/0.56          | ~ (v1_tsep_1 @ X21 @ X22)
% 0.38/0.56          | ~ (m1_pre_topc @ X21 @ X22))),
% 0.38/0.56      inference('simplify', [status(thm)], ['118'])).
% 0.38/0.56  thf('120', plain,
% 0.38/0.56      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.38/0.56        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.38/0.56        | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_D)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['117', '119'])).
% 0.38/0.56  thf('121', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('122', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('123', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('124', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('125', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X9 @ X10)
% 0.38/0.56          | (v2_pre_topc @ X9)
% 0.38/0.56          | ~ (l1_pre_topc @ X10)
% 0.38/0.56          | ~ (v2_pre_topc @ X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.56  thf('126', plain,
% 0.38/0.56      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.56  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('129', plain, ((v2_pre_topc @ sk_D)),
% 0.38/0.56      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.38/0.56  thf('130', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)),
% 0.38/0.56      inference('demod', [status(thm)], ['120', '121', '122', '123', '129'])).
% 0.38/0.56  thf('131', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_B)
% 0.38/0.56        | (v2_struct_0 @ sk_D)
% 0.38/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.56        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56        | (v2_struct_0 @ sk_C_1)
% 0.38/0.56        | (v2_struct_0 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['114', '116', '130'])).
% 0.38/0.56  thf('132', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56        | (v2_struct_0 @ sk_A)
% 0.38/0.56        | (v2_struct_0 @ sk_C_1)
% 0.38/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.56        | (v2_struct_0 @ sk_D)
% 0.38/0.56        | (v2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['42', '131'])).
% 0.38/0.56  thf('133', plain,
% 0.38/0.56      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.38/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.56      inference('split', [status(esa)], ['56'])).
% 0.38/0.56  thf('134', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['57', '92'])).
% 0.38/0.56  thf('135', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.38/0.56  thf('136', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_B)
% 0.38/0.56        | (v2_struct_0 @ sk_D)
% 0.38/0.56        | (v2_struct_0 @ sk_C_1)
% 0.38/0.56        | (v2_struct_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['132', '135'])).
% 0.38/0.56  thf('137', plain,
% 0.38/0.56      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '28'])).
% 0.38/0.56  thf(t5_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.56  thf('138', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X6 @ X7)
% 0.38/0.56          | ~ (v1_xboole_0 @ X8)
% 0.38/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.56  thf('139', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['137', '138'])).
% 0.38/0.56  thf('140', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ sk_A)
% 0.38/0.56          | (v2_struct_0 @ sk_C_1)
% 0.38/0.56          | (v2_struct_0 @ sk_D)
% 0.38/0.56          | (v2_struct_0 @ sk_B)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['136', '139'])).
% 0.38/0.56  thf('141', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_B)
% 0.38/0.56        | (v2_struct_0 @ sk_D)
% 0.38/0.56        | (v2_struct_0 @ sk_C_1)
% 0.38/0.56        | (v2_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['39', '140'])).
% 0.38/0.56  thf('142', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('143', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['141', '142'])).
% 0.38/0.56  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('145', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['143', '144'])).
% 0.38/0.56  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('147', plain, ((v2_struct_0 @ sk_C_1)),
% 0.38/0.56      inference('clc', [status(thm)], ['145', '146'])).
% 0.38/0.56  thf('148', plain, ($false), inference('demod', [status(thm)], ['0', '147'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
