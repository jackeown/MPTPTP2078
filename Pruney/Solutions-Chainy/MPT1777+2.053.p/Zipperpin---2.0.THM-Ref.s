%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iqvDVsgoTG

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:34 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  190 (2007 expanded)
%              Number of leaves         :   37 ( 571 expanded)
%              Depth                    :   28
%              Number of atoms          : 1774 (61721 expanded)
%              Number of equality atoms :   28 (1638 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_connsp_2 @ ( sk_C @ X16 @ X15 ) @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('3',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('6',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['3','9','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_connsp_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('22',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X27 ) )
      | ( m1_pre_topc @ X25 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ( m1_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','54'])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('68',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(t22_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_pre_topc @ X17 @ ( k1_tsep_1 @ X18 @ X17 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('77',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['50','51'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['74','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','83'])).

thf('85',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('89',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k1_tsep_1 @ X24 @ X23 @ X23 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('92',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['50','51'])).

thf('93',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 )
      = sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 )
      = sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 )
    = sk_D ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['87','97'])).

thf('99',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','98'])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','100'])).

thf('102',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('107',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

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

thf('109',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_tmap_1 @ X34 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37 ) @ X36 )
      | ( r1_tmap_1 @ X32 @ X31 @ X37 @ X38 )
      | ( X38 != X36 )
      | ~ ( m1_connsp_2 @ X35 @ X32 @ X38 )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('110',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_connsp_2 @ X35 @ X32 @ X36 )
      | ( r1_tmap_1 @ X32 @ X31 @ X37 @ X36 )
      | ~ ( r1_tmap_1 @ X34 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
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
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('113',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('114',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('115',plain,(
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
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
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
    inference('sup-',[status(thm)],['107','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('120',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
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
    inference(demod,[status(thm)],['116','117','120','121','122'])).

thf('124',plain,(
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
    inference('sup-',[status(thm)],['104','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['87','97'])).

thf('127',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('131',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126','129','130','131','132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','134'])).

thf('136',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('137',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('138',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','99'])).

thf('140',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['135','140','141'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['0','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iqvDVsgoTG
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 832 iterations in 0.402s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.86  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.67/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.67/0.86  thf(sk_E_type, type, sk_E: $i).
% 0.67/0.86  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.67/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.86  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.86  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.67/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.67/0.86  thf(sk_F_type, type, sk_F: $i).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(sk_G_type, type, sk_G: $i).
% 0.67/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.86  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.67/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.86  thf(t88_tmap_1, conjecture,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.67/0.86             ( l1_pre_topc @ B ) ) =>
% 0.67/0.86           ( ![C:$i]:
% 0.67/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.86               ( ![D:$i]:
% 0.67/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.67/0.86                   ( ![E:$i]:
% 0.67/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.67/0.86                         ( v1_funct_2 @
% 0.67/0.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.86                         ( m1_subset_1 @
% 0.67/0.86                           E @ 
% 0.67/0.86                           ( k1_zfmisc_1 @
% 0.67/0.86                             ( k2_zfmisc_1 @
% 0.67/0.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.86                       ( ( ( g1_pre_topc @
% 0.67/0.86                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.67/0.86                           ( D ) ) =>
% 0.67/0.86                         ( ![F:$i]:
% 0.67/0.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.67/0.86                             ( ![G:$i]:
% 0.67/0.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.67/0.86                                 ( ( ( ( F ) = ( G ) ) & 
% 0.67/0.86                                     ( r1_tmap_1 @
% 0.67/0.86                                       C @ B @ 
% 0.67/0.86                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.67/0.86                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i]:
% 0.67/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.86            ( l1_pre_topc @ A ) ) =>
% 0.67/0.86          ( ![B:$i]:
% 0.67/0.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.67/0.86                ( l1_pre_topc @ B ) ) =>
% 0.67/0.86              ( ![C:$i]:
% 0.67/0.86                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.86                  ( ![D:$i]:
% 0.67/0.86                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.67/0.86                      ( ![E:$i]:
% 0.67/0.86                        ( ( ( v1_funct_1 @ E ) & 
% 0.67/0.86                            ( v1_funct_2 @
% 0.67/0.86                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.86                            ( m1_subset_1 @
% 0.67/0.86                              E @ 
% 0.67/0.86                              ( k1_zfmisc_1 @
% 0.67/0.86                                ( k2_zfmisc_1 @
% 0.67/0.86                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.86                          ( ( ( g1_pre_topc @
% 0.67/0.86                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.67/0.86                              ( D ) ) =>
% 0.67/0.86                            ( ![F:$i]:
% 0.67/0.86                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.67/0.86                                ( ![G:$i]:
% 0.67/0.86                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.67/0.86                                    ( ( ( ( F ) = ( G ) ) & 
% 0.67/0.86                                        ( r1_tmap_1 @
% 0.67/0.86                                          C @ B @ 
% 0.67/0.86                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.67/0.86                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.67/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(existence_m1_connsp_2, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.86         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      (![X15 : $i, X16 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X15)
% 0.67/0.86          | ~ (v2_pre_topc @ X15)
% 0.67/0.86          | (v2_struct_0 @ X15)
% 0.67/0.86          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.67/0.86          | (m1_connsp_2 @ (sk_C @ X16 @ X15) @ X15 @ X16))),
% 0.67/0.86      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.67/0.86  thf('3', plain,
% 0.67/0.86      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.67/0.86        | (v2_struct_0 @ sk_D)
% 0.67/0.86        | ~ (v2_pre_topc @ sk_D)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.86  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(cc1_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X6 @ X7)
% 0.67/0.86          | (v2_pre_topc @ X6)
% 0.67/0.86          | ~ (l1_pre_topc @ X7)
% 0.67/0.86          | ~ (v2_pre_topc @ X7))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.86  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('9', plain, ((v2_pre_topc @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.67/0.86  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(dt_m1_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.67/0.86  thf('11', plain,
% 0.67/0.86      (![X8 : $i, X9 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['10', '11'])).
% 0.67/0.86  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['12', '13'])).
% 0.67/0.86  thf('15', plain,
% 0.67/0.86      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.67/0.86        | (v2_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['3', '9', '14'])).
% 0.67/0.86  thf('16', plain, (~ (v2_struct_0 @ sk_D)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('17', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.67/0.86      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.86  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(dt_m1_connsp_2, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.86         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.86       ( ![C:$i]:
% 0.67/0.86         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.67/0.86           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.86         (~ (l1_pre_topc @ X12)
% 0.67/0.86          | ~ (v2_pre_topc @ X12)
% 0.67/0.86          | (v2_struct_0 @ X12)
% 0.67/0.86          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.67/0.86          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.67/0.86          | ~ (m1_connsp_2 @ X14 @ X12 @ X13))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.67/0.86          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | ~ (v2_pre_topc @ sk_D)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.86  thf('21', plain, ((v2_pre_topc @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.67/0.86  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['12', '13'])).
% 0.67/0.86  thf('23', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.67/0.86          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.67/0.86          | (v2_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.67/0.86  thf('24', plain, (~ (v2_struct_0 @ sk_D)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('25', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.67/0.86          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.67/0.86      inference('clc', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf('26', plain,
% 0.67/0.86      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['17', '25'])).
% 0.67/0.86  thf('27', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t4_tsep_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.86           ( ![C:$i]:
% 0.67/0.86             ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.86               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.67/0.86                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.67/0.86  thf('29', plain,
% 0.67/0.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X25 @ X26)
% 0.67/0.86          | ~ (m1_pre_topc @ X25 @ X27)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X27))
% 0.67/0.86          | ~ (m1_pre_topc @ X27 @ X26)
% 0.67/0.86          | ~ (l1_pre_topc @ X26)
% 0.67/0.86          | ~ (v2_pre_topc @ X26))),
% 0.67/0.86      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.67/0.86  thf('30', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v2_pre_topc @ sk_A)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.86  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('33', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ X0))),
% 0.67/0.86      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.67/0.86  thf('34', plain,
% 0.67/0.86      ((~ (m1_pre_topc @ sk_D @ sk_C_1)
% 0.67/0.86        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['27', '33'])).
% 0.67/0.86  thf('35', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(d10_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.86  thf('36', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.86      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.86  thf('38', plain,
% 0.67/0.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X25 @ X26)
% 0.67/0.86          | ~ (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X27))
% 0.67/0.86          | (m1_pre_topc @ X25 @ X27)
% 0.67/0.86          | ~ (m1_pre_topc @ X27 @ X26)
% 0.67/0.86          | ~ (l1_pre_topc @ X26)
% 0.67/0.86          | ~ (v2_pre_topc @ X26))),
% 0.67/0.86      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.67/0.86  thf('39', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (v2_pre_topc @ X1)
% 0.67/0.86          | ~ (l1_pre_topc @ X1)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.67/0.86          | (m1_pre_topc @ X0 @ X0)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.86  thf('40', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((m1_pre_topc @ X0 @ X0)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.67/0.86          | ~ (l1_pre_topc @ X1)
% 0.67/0.86          | ~ (v2_pre_topc @ X1))),
% 0.67/0.86      inference('simplify', [status(thm)], ['39'])).
% 0.67/0.86  thf('41', plain,
% 0.67/0.86      ((~ (v2_pre_topc @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (m1_pre_topc @ sk_D @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['35', '40'])).
% 0.67/0.86  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.67/0.86  thf('45', plain,
% 0.67/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.67/0.86         = (sk_D))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t59_pre_topc, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( l1_pre_topc @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_pre_topc @
% 0.67/0.86             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.67/0.86           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.67/0.86  thf('46', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X10 @ 
% 0.67/0.86             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.67/0.86          | (m1_pre_topc @ X10 @ X11)
% 0.67/0.86          | ~ (l1_pre_topc @ X11))),
% 0.67/0.86      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.67/0.86  thf('47', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_C_1)
% 0.67/0.86          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['45', '46'])).
% 0.67/0.86  thf('48', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('49', plain,
% 0.67/0.86      (![X8 : $i, X9 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('50', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['48', '49'])).
% 0.67/0.86  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('52', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['50', '51'])).
% 0.67/0.86  thf('53', plain,
% 0.67/0.86      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['47', '52'])).
% 0.67/0.86  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.67/0.86      inference('sup-', [status(thm)], ['44', '53'])).
% 0.67/0.86  thf('55', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['34', '54'])).
% 0.67/0.86  thf('56', plain,
% 0.67/0.86      (![X0 : $i, X2 : $i]:
% 0.67/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('57', plain,
% 0.67/0.86      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.67/0.86        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['55', '56'])).
% 0.67/0.86  thf('58', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('59', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('60', plain,
% 0.67/0.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X25 @ X26)
% 0.67/0.86          | ~ (m1_pre_topc @ X25 @ X27)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X27))
% 0.67/0.86          | ~ (m1_pre_topc @ X27 @ X26)
% 0.67/0.86          | ~ (l1_pre_topc @ X26)
% 0.67/0.86          | ~ (v2_pre_topc @ X26))),
% 0.67/0.86      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.67/0.86  thf('61', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v2_pre_topc @ sk_A)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['59', '60'])).
% 0.67/0.86  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('64', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.67/0.86          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.67/0.86      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.67/0.86  thf('65', plain,
% 0.67/0.86      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.67/0.86        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['58', '64'])).
% 0.67/0.86  thf('66', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('67', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((m1_pre_topc @ X0 @ X0)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.67/0.86          | ~ (l1_pre_topc @ X1)
% 0.67/0.86          | ~ (v2_pre_topc @ X1))),
% 0.67/0.86      inference('simplify', [status(thm)], ['39'])).
% 0.67/0.86  thf('68', plain,
% 0.67/0.86      ((~ (v2_pre_topc @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['66', '67'])).
% 0.67/0.86  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('71', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.67/0.86  thf('72', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.67/0.86  thf(t22_tsep_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.67/0.86           ( ![C:$i]:
% 0.67/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.86               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.67/0.86  thf('73', plain,
% 0.67/0.86      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X17)
% 0.67/0.86          | ~ (m1_pre_topc @ X17 @ X18)
% 0.67/0.86          | (m1_pre_topc @ X17 @ (k1_tsep_1 @ X18 @ X17 @ X19))
% 0.67/0.86          | ~ (m1_pre_topc @ X19 @ X18)
% 0.67/0.86          | (v2_struct_0 @ X19)
% 0.67/0.86          | ~ (l1_pre_topc @ X18)
% 0.67/0.86          | ~ (v2_pre_topc @ X18)
% 0.67/0.86          | (v2_struct_0 @ X18))),
% 0.67/0.86      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.67/0.86  thf('74', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v2_struct_0 @ sk_C_1)
% 0.67/0.86          | ~ (v2_pre_topc @ sk_C_1)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_C_1)
% 0.67/0.86          | (v2_struct_0 @ X0)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.67/0.86          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.67/0.86          | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['72', '73'])).
% 0.67/0.86  thf('75', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('76', plain,
% 0.67/0.86      (![X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X6 @ X7)
% 0.67/0.86          | (v2_pre_topc @ X6)
% 0.67/0.86          | ~ (l1_pre_topc @ X7)
% 0.67/0.86          | ~ (v2_pre_topc @ X7))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.67/0.86  thf('77', plain,
% 0.67/0.86      ((~ (v2_pre_topc @ sk_A)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86        | (v2_pre_topc @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['75', '76'])).
% 0.67/0.86  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('80', plain, ((v2_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.67/0.86  thf('81', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['50', '51'])).
% 0.67/0.86  thf('82', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v2_struct_0 @ sk_C_1)
% 0.67/0.86          | (v2_struct_0 @ X0)
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.67/0.86          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.67/0.86          | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['74', '80', '81'])).
% 0.67/0.86  thf('83', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.67/0.86          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.67/0.86          | (v2_struct_0 @ X0)
% 0.67/0.86          | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('simplify', [status(thm)], ['82'])).
% 0.67/0.86  thf('84', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_C_1)
% 0.67/0.86        | (v2_struct_0 @ sk_C_1)
% 0.67/0.86        | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['71', '83'])).
% 0.67/0.86  thf('85', plain,
% 0.67/0.86      (((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.67/0.86        | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('simplify', [status(thm)], ['84'])).
% 0.67/0.86  thf('86', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('87', plain,
% 0.67/0.86      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.67/0.86      inference('clc', [status(thm)], ['85', '86'])).
% 0.67/0.86  thf('88', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.67/0.86  thf(t25_tmap_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.67/0.86           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.67/0.86             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.67/0.86  thf('89', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X23)
% 0.67/0.86          | ~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.86          | ((k1_tsep_1 @ X24 @ X23 @ X23)
% 0.67/0.86              = (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.67/0.86          | ~ (l1_pre_topc @ X24)
% 0.67/0.86          | ~ (v2_pre_topc @ X24)
% 0.67/0.86          | (v2_struct_0 @ X24))),
% 0.67/0.86      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.67/0.86  thf('90', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_C_1)
% 0.67/0.86        | ~ (v2_pre_topc @ sk_C_1)
% 0.67/0.86        | ~ (l1_pre_topc @ sk_C_1)
% 0.67/0.86        | ((k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)
% 0.67/0.86            = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.86        | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('sup-', [status(thm)], ['88', '89'])).
% 0.67/0.86  thf('91', plain, ((v2_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.67/0.86  thf('92', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.86      inference('demod', [status(thm)], ['50', '51'])).
% 0.67/0.86  thf('93', plain,
% 0.67/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.67/0.86         = (sk_D))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('94', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_C_1)
% 0.67/0.86        | ((k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) = (sk_D))
% 0.67/0.86        | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.67/0.86  thf('95', plain,
% 0.67/0.86      ((((k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) = (sk_D))
% 0.67/0.86        | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('simplify', [status(thm)], ['94'])).
% 0.67/0.86  thf('96', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('97', plain, (((k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) = (sk_D))),
% 0.67/0.86      inference('clc', [status(thm)], ['95', '96'])).
% 0.67/0.86  thf('98', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['87', '97'])).
% 0.67/0.86  thf('99', plain,
% 0.67/0.86      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['65', '98'])).
% 0.67/0.86  thf('100', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('101', plain,
% 0.67/0.86      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.67/0.86      inference('demod', [status(thm)], ['26', '100'])).
% 0.67/0.86  thf('102', plain,
% 0.67/0.86      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.67/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('103', plain, (((sk_F) = (sk_G))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('104', plain,
% 0.67/0.86      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.67/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.67/0.86      inference('demod', [status(thm)], ['102', '103'])).
% 0.67/0.86  thf('105', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_E @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('106', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('107', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_E @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['105', '106'])).
% 0.67/0.86  thf('108', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf(t83_tmap_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.67/0.86             ( l1_pre_topc @ B ) ) =>
% 0.67/0.86           ( ![C:$i]:
% 0.67/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.86               ( ![D:$i]:
% 0.67/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.67/0.86                   ( ![E:$i]:
% 0.67/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.67/0.86                         ( v1_funct_2 @
% 0.67/0.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.86                         ( m1_subset_1 @
% 0.67/0.86                           E @ 
% 0.67/0.86                           ( k1_zfmisc_1 @
% 0.67/0.86                             ( k2_zfmisc_1 @
% 0.67/0.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.86                       ( ( m1_pre_topc @ C @ D ) =>
% 0.67/0.86                         ( ![F:$i]:
% 0.67/0.86                           ( ( m1_subset_1 @
% 0.67/0.86                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.67/0.86                             ( ![G:$i]:
% 0.67/0.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.67/0.86                                 ( ![H:$i]:
% 0.67/0.86                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.67/0.86                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.67/0.86                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.67/0.86                                         ( ( G ) = ( H ) ) ) =>
% 0.67/0.86                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.67/0.86                                         ( r1_tmap_1 @
% 0.67/0.86                                           C @ B @ 
% 0.67/0.86                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.67/0.86                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.86  thf('109', plain,
% 0.67/0.86      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 0.67/0.86         X38 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X31)
% 0.67/0.86          | ~ (v2_pre_topc @ X31)
% 0.67/0.86          | ~ (l1_pre_topc @ X31)
% 0.67/0.86          | (v2_struct_0 @ X32)
% 0.67/0.86          | ~ (m1_pre_topc @ X32 @ X33)
% 0.67/0.86          | ~ (m1_pre_topc @ X34 @ X32)
% 0.67/0.86          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.67/0.86          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.67/0.86          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 0.67/0.86               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 0.67/0.86          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X38)
% 0.67/0.86          | ((X38) != (X36))
% 0.67/0.86          | ~ (m1_connsp_2 @ X35 @ X32 @ X38)
% 0.67/0.86          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X34))
% 0.67/0.86          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X32))
% 0.67/0.86          | ~ (m1_subset_1 @ X37 @ 
% 0.67/0.86               (k1_zfmisc_1 @ 
% 0.67/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 0.67/0.86          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 0.67/0.86          | ~ (v1_funct_1 @ X37)
% 0.67/0.86          | ~ (m1_pre_topc @ X34 @ X33)
% 0.67/0.86          | (v2_struct_0 @ X34)
% 0.67/0.86          | ~ (l1_pre_topc @ X33)
% 0.67/0.86          | ~ (v2_pre_topc @ X33)
% 0.67/0.86          | (v2_struct_0 @ X33))),
% 0.67/0.86      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.67/0.86  thf('110', plain,
% 0.67/0.86      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X33)
% 0.67/0.86          | ~ (v2_pre_topc @ X33)
% 0.67/0.86          | ~ (l1_pre_topc @ X33)
% 0.67/0.86          | (v2_struct_0 @ X34)
% 0.67/0.86          | ~ (m1_pre_topc @ X34 @ X33)
% 0.67/0.86          | ~ (v1_funct_1 @ X37)
% 0.67/0.86          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 0.67/0.86          | ~ (m1_subset_1 @ X37 @ 
% 0.67/0.86               (k1_zfmisc_1 @ 
% 0.67/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 0.67/0.86          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X32))
% 0.67/0.86          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X34))
% 0.67/0.86          | ~ (m1_connsp_2 @ X35 @ X32 @ X36)
% 0.67/0.86          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X36)
% 0.67/0.86          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 0.67/0.86               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 0.67/0.86          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.67/0.86          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.67/0.86          | ~ (m1_pre_topc @ X34 @ X32)
% 0.67/0.86          | ~ (m1_pre_topc @ X32 @ X33)
% 0.67/0.86          | (v2_struct_0 @ X32)
% 0.67/0.86          | ~ (l1_pre_topc @ X31)
% 0.67/0.86          | ~ (v2_pre_topc @ X31)
% 0.67/0.86          | (v2_struct_0 @ X31))),
% 0.67/0.86      inference('simplify', [status(thm)], ['109'])).
% 0.67/0.86  thf('111', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X1 @ 
% 0.67/0.86             (k1_zfmisc_1 @ 
% 0.67/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.67/0.86          | (v2_struct_0 @ X0)
% 0.67/0.86          | ~ (v2_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.67/0.86          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.67/0.86          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.67/0.86          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.67/0.86          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.67/0.86               X5)
% 0.67/0.86          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.67/0.86          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.67/0.86          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.67/0.86          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.67/0.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ X1)
% 0.67/0.86          | ~ (m1_pre_topc @ X3 @ X2)
% 0.67/0.86          | (v2_struct_0 @ X3)
% 0.67/0.86          | ~ (l1_pre_topc @ X2)
% 0.67/0.86          | ~ (v2_pre_topc @ X2)
% 0.67/0.86          | (v2_struct_0 @ X2))),
% 0.67/0.86      inference('sup-', [status(thm)], ['108', '110'])).
% 0.67/0.86  thf('112', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('113', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('114', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('115', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X1 @ 
% 0.67/0.86             (k1_zfmisc_1 @ 
% 0.67/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.67/0.86          | (v2_struct_0 @ X0)
% 0.67/0.86          | ~ (v2_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.67/0.86          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.67/0.86          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.67/0.86          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.67/0.86               X5)
% 0.67/0.86          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.67/0.86          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.67/0.86          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.67/0.86          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ X1)
% 0.67/0.86          | ~ (m1_pre_topc @ X3 @ X2)
% 0.67/0.86          | (v2_struct_0 @ X3)
% 0.67/0.86          | ~ (l1_pre_topc @ X2)
% 0.67/0.86          | ~ (v2_pre_topc @ X2)
% 0.67/0.86          | (v2_struct_0 @ X2))),
% 0.67/0.86      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.67/0.86  thf('116', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X0)
% 0.67/0.86          | ~ (v2_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | (v2_struct_0 @ X1)
% 0.67/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.67/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.86               (u1_struct_0 @ sk_B))
% 0.67/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.67/0.86          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.67/0.86          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.67/0.86          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.67/0.86               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.67/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.67/0.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.67/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.67/0.86          | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['107', '115'])).
% 0.67/0.86  thf('117', plain, ((v1_funct_1 @ sk_E)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('118', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('119', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('120', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['118', '119'])).
% 0.67/0.86  thf('121', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('122', plain, ((v2_pre_topc @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('123', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X0)
% 0.67/0.86          | ~ (v2_pre_topc @ X0)
% 0.67/0.86          | ~ (l1_pre_topc @ X0)
% 0.67/0.86          | (v2_struct_0 @ X1)
% 0.67/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.67/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.67/0.86          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.67/0.86          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.67/0.86          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.67/0.86               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.67/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.67/0.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['116', '117', '120', '121', '122'])).
% 0.67/0.86  thf('124', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v2_struct_0 @ sk_B)
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.67/0.86          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.67/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.67/0.86          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.67/0.86          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.67/0.86          | (v2_struct_0 @ sk_C_1)
% 0.67/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.67/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.67/0.86          | (v2_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['104', '123'])).
% 0.67/0.86  thf('125', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('126', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['87', '97'])).
% 0.67/0.86  thf('127', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('128', plain, (((sk_F) = (sk_G))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('129', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['127', '128'])).
% 0.67/0.86  thf('130', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['127', '128'])).
% 0.67/0.86  thf('131', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('134', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v2_struct_0 @ sk_B)
% 0.67/0.86          | (v2_struct_0 @ sk_D)
% 0.67/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.86          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.67/0.86          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.67/0.86          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86          | (v2_struct_0 @ sk_C_1)
% 0.67/0.86          | (v2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)],
% 0.67/0.86                ['124', '125', '126', '129', '130', '131', '132', '133'])).
% 0.67/0.86  thf('135', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_A)
% 0.67/0.86        | (v2_struct_0 @ sk_C_1)
% 0.67/0.86        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.67/0.86        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.67/0.86        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.67/0.86        | (v2_struct_0 @ sk_D)
% 0.67/0.86        | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['101', '134'])).
% 0.67/0.86  thf('136', plain,
% 0.67/0.86      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['17', '25'])).
% 0.67/0.86  thf(t3_subset, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.86  thf('137', plain,
% 0.67/0.86      (![X3 : $i, X4 : $i]:
% 0.67/0.86         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('138', plain,
% 0.67/0.86      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['136', '137'])).
% 0.67/0.86  thf('139', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.67/0.86      inference('demod', [status(thm)], ['57', '99'])).
% 0.67/0.86  thf('140', plain,
% 0.67/0.86      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('demod', [status(thm)], ['138', '139'])).
% 0.67/0.86  thf('141', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.67/0.86      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.86  thf('142', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_A)
% 0.67/0.86        | (v2_struct_0 @ sk_C_1)
% 0.67/0.86        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.67/0.86        | (v2_struct_0 @ sk_D)
% 0.67/0.86        | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['135', '140', '141'])).
% 0.67/0.86  thf('143', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('144', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_B)
% 0.67/0.86        | (v2_struct_0 @ sk_D)
% 0.67/0.86        | (v2_struct_0 @ sk_C_1)
% 0.67/0.86        | (v2_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['142', '143'])).
% 0.67/0.86  thf('145', plain, (~ (v2_struct_0 @ sk_D)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('146', plain,
% 0.67/0.86      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['144', '145'])).
% 0.67/0.86  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('148', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.67/0.86      inference('clc', [status(thm)], ['146', '147'])).
% 0.67/0.86  thf('149', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('150', plain, ((v2_struct_0 @ sk_C_1)),
% 0.67/0.86      inference('clc', [status(thm)], ['148', '149'])).
% 0.67/0.86  thf('151', plain, ($false), inference('demod', [status(thm)], ['0', '150'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
