%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lLaQmjLmkV

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:22 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  278 (5440 expanded)
%              Number of leaves         :   40 (1555 expanded)
%              Depth                    :   35
%              Number of atoms          : 3322 (177761 expanded)
%              Number of equality atoms :   15 (2364 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_connsp_2 @ ( sk_C @ X17 @ X16 ) @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('9',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','12','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['18','19'])).

thf('22',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_connsp_2 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_C_1 @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('26',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_C_1 @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( r2_hidden @ X18 @ ( sk_D @ X20 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ X0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('34',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ X0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,
    ( ( r2_hidden @ sk_F @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ sk_F @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['18','19'])).

thf('42',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( m1_subset_1 @ ( sk_D @ X20 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('46',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v3_pre_topc @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_C_1 @ X1 )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('59',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['18','19'])).

thf('61',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( v3_pre_topc @ ( sk_D @ X20 @ X18 @ X19 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ X0 @ sk_C_1 ) @ sk_C_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('65',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ X0 @ sk_C_1 ) @ sk_C_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_C_1 @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( m1_subset_1 @ ( sk_D @ X20 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('89',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('90',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('94',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['96','101'])).

thf('103',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('111',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['103'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('113',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_pre_topc @ X31 @ X34 )
      | ~ ( r1_tmap_1 @ X34 @ X30 @ X35 @ X33 )
      | ( X33 != X36 )
      | ( r1_tmap_1 @ X31 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('114',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X31 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35 ) @ X36 )
      | ~ ( r1_tmap_1 @ X34 @ X30 @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X31 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['110','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['109','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['107'])).

thf('133',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['103'])).

thf('145',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['108','143','144'])).

thf('146',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['106','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('148',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ~ ( r1_tmap_1 @ X40 @ X37 @ ( k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43 ) @ X42 )
      | ( r1_tmap_1 @ X38 @ X37 @ X43 @ X44 )
      | ( X44 != X42 )
      | ~ ( r1_tarski @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( r2_hidden @ X44 @ X41 )
      | ~ ( v3_pre_topc @ X41 @ X38 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('149',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v3_pre_topc @ X41 @ X38 )
      | ~ ( r2_hidden @ X42 @ X41 )
      | ~ ( r1_tarski @ X41 @ ( u1_struct_0 @ X40 ) )
      | ( r1_tmap_1 @ X38 @ X37 @ X43 @ X42 )
      | ~ ( r1_tmap_1 @ X40 @ X37 @ ( k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_pre_topc @ X40 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','149'])).

thf('151',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('162',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161','162','163'])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_F @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','164'])).

thf('166',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('167',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('168',plain,(
    r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['81','82'])).

thf('170',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('171',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( r2_hidden @ X18 @ ( sk_D @ X20 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('175',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('176',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('177',plain,
    ( ( r2_hidden @ sk_F @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    r2_hidden @ sk_F @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('181',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['96','101'])).

thf('182',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('183',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('184',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('186',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf(t9_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( ( v3_pre_topc @ C @ A )
                          & ( r1_tarski @ C @ ( u1_struct_0 @ B ) )
                          & ( r1_tarski @ D @ C )
                          & ( D = E ) )
                       => ( ( v3_pre_topc @ E @ B )
                        <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) )).

thf('187',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v3_pre_topc @ X48 @ X46 )
      | ~ ( r1_tarski @ X48 @ ( u1_struct_0 @ X45 ) )
      | ~ ( r1_tarski @ X47 @ X48 )
      | ( X47 != X49 )
      | ~ ( v3_pre_topc @ X49 @ X45 )
      | ( v3_pre_topc @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t9_tsep_1])).

thf('188',plain,(
    ! [X45: $i,X46: $i,X48: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( v3_pre_topc @ X49 @ X46 )
      | ~ ( v3_pre_topc @ X49 @ X45 )
      | ~ ( r1_tarski @ X49 @ X48 )
      | ~ ( r1_tarski @ X48 @ ( u1_struct_0 @ X45 ) )
      | ~ ( v3_pre_topc @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( m1_pre_topc @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( v3_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['186','188'])).

thf('190',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

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

thf('191',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( X24
       != ( u1_struct_0 @ X22 ) )
      | ~ ( v1_tsep_1 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v3_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('192',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X22 ) @ X23 )
      | ~ ( v1_tsep_1 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['190','192'])).

thf('194',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('197',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('199',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['193','194','195','196','202'])).

thf('204',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('205',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( v3_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['189','203','204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_D_1 )
      | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['181','206'])).

thf('208',plain,(
    r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_D_1 )
      | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 )
    | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['180','209'])).

thf('211',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('213',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_C_1 @ sk_F ),
    inference(clc,[status(thm)],['81','82'])).

thf('214',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('215',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( v3_pre_topc @ ( sk_D @ X20 @ X18 @ X19 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) @ X0 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('218',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('219',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('220',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('221',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_C_1 ) @ sk_F @ sk_C_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['210','211','212','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','168','179','224'])).

thf('226',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['107'])).

thf('227',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['108','143'])).

thf('228',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    $false ),
    inference(demod,[status(thm)],['0','235'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lLaQmjLmkV
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 471 iterations in 0.240s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.69  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.47/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.47/0.69  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.47/0.69  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.47/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(sk_G_type, type, sk_G: $i).
% 0.47/0.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.69  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.69  thf(t86_tmap_1, conjecture,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.69       ( ![B:$i]:
% 0.47/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.69             ( l1_pre_topc @ B ) ) =>
% 0.47/0.69           ( ![C:$i]:
% 0.47/0.69             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.69               ( ![D:$i]:
% 0.47/0.69                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.69                   ( ![E:$i]:
% 0.47/0.69                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.69                         ( v1_funct_2 @
% 0.47/0.69                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.69                         ( m1_subset_1 @
% 0.47/0.69                           E @ 
% 0.47/0.69                           ( k1_zfmisc_1 @
% 0.47/0.69                             ( k2_zfmisc_1 @
% 0.47/0.69                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.69                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.47/0.69                         ( ![F:$i]:
% 0.47/0.69                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.69                             ( ![G:$i]:
% 0.47/0.69                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.69                                 ( ( ( F ) = ( G ) ) =>
% 0.47/0.69                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.47/0.69                                     ( r1_tmap_1 @
% 0.47/0.69                                       C @ B @ 
% 0.47/0.69                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i]:
% 0.47/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.69            ( l1_pre_topc @ A ) ) =>
% 0.47/0.69          ( ![B:$i]:
% 0.47/0.69            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.69                ( l1_pre_topc @ B ) ) =>
% 0.47/0.69              ( ![C:$i]:
% 0.47/0.69                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.69                  ( ![D:$i]:
% 0.47/0.69                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.69                      ( ![E:$i]:
% 0.47/0.69                        ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.69                            ( v1_funct_2 @
% 0.47/0.69                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.69                            ( m1_subset_1 @
% 0.47/0.69                              E @ 
% 0.47/0.69                              ( k1_zfmisc_1 @
% 0.47/0.69                                ( k2_zfmisc_1 @
% 0.47/0.69                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.69                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.47/0.69                            ( ![F:$i]:
% 0.47/0.69                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.69                                ( ![G:$i]:
% 0.47/0.69                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.69                                    ( ( ( F ) = ( G ) ) =>
% 0.47/0.69                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.47/0.69                                        ( r1_tmap_1 @
% 0.47/0.69                                          C @ B @ 
% 0.47/0.69                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.47/0.69  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('3', plain, (((sk_F) = (sk_G))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf(existence_m1_connsp_2, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.69         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.69       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         (~ (l1_pre_topc @ X16)
% 0.47/0.69          | ~ (v2_pre_topc @ X16)
% 0.47/0.69          | (v2_struct_0 @ X16)
% 0.47/0.69          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.47/0.69          | (m1_connsp_2 @ (sk_C @ X17 @ X16) @ X16 @ X17))),
% 0.47/0.69      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.47/0.69        | (v2_struct_0 @ sk_C_1)
% 0.47/0.69        | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69        | ~ (l1_pre_topc @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.69  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(cc1_pre_topc, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X6 : $i, X7 : $i]:
% 0.47/0.69         (~ (m1_pre_topc @ X6 @ X7)
% 0.47/0.69          | (v2_pre_topc @ X6)
% 0.47/0.69          | ~ (l1_pre_topc @ X7)
% 0.47/0.69          | ~ (v2_pre_topc @ X7))),
% 0.47/0.69      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      ((~ (v2_pre_topc @ sk_A)
% 0.47/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.69        | (v2_pre_topc @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.69  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('12', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(dt_m1_pre_topc, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( l1_pre_topc @ A ) =>
% 0.47/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X8 : $i, X9 : $i]:
% 0.47/0.69         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.69  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.69  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['6', '12', '17'])).
% 0.47/0.69  thf('19', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.47/0.69  thf('21', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.47/0.69  thf('22', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf(dt_m1_connsp_2, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.69         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.69       ( ![C:$i]:
% 0.47/0.69         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.47/0.69           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.69         (~ (l1_pre_topc @ X13)
% 0.47/0.69          | ~ (v2_pre_topc @ X13)
% 0.47/0.69          | (v2_struct_0 @ X13)
% 0.47/0.69          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.47/0.69          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.47/0.69          | ~ (m1_connsp_2 @ X15 @ X13 @ X14))),
% 0.47/0.69      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F)
% 0.47/0.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | (v2_struct_0 @ sk_C_1)
% 0.47/0.69          | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69          | ~ (l1_pre_topc @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.69  thf('25', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('26', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('27', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F)
% 0.47/0.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.69  thf('28', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | ~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F))),
% 0.47/0.69      inference('clc', [status(thm)], ['27', '28'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['21', '29'])).
% 0.47/0.69  thf(t8_connsp_2, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.69       ( ![B:$i]:
% 0.47/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.69           ( ![C:$i]:
% 0.47/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.69               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.47/0.69                 ( ?[D:$i]:
% 0.47/0.69                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.47/0.69                     ( v3_pre_topc @ D @ A ) & 
% 0.47/0.69                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.69          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.69          | (r2_hidden @ X18 @ (sk_D @ X20 @ X18 @ X19))
% 0.47/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (l1_pre_topc @ X19)
% 0.47/0.69          | ~ (v2_pre_topc @ X19)
% 0.47/0.69          | (v2_struct_0 @ X19))),
% 0.47/0.69      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69          | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.69          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ X0 @ sk_C_1))
% 0.47/0.69          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.69  thf('33', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('34', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ X0 @ sk_C_1))
% 0.47/0.69          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.69        | (r2_hidden @ sk_F @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['20', '35'])).
% 0.47/0.69  thf('37', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      (((r2_hidden @ sk_F @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.69  thf('39', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      ((r2_hidden @ sk_F @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))),
% 0.47/0.69      inference('clc', [status(thm)], ['38', '39'])).
% 0.47/0.69  thf('41', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['21', '29'])).
% 0.47/0.69  thf('43', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.69          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.69          | (m1_subset_1 @ (sk_D @ X20 @ X18 @ X19) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (l1_pre_topc @ X19)
% 0.47/0.69          | ~ (v2_pre_topc @ X19)
% 0.47/0.69          | (v2_struct_0 @ X19))),
% 0.47/0.69      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.69  thf('44', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69          | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.69          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ X0 @ sk_C_1) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.69  thf('45', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('46', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ X0 @ sk_C_1) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.47/0.69  thf('48', plain,
% 0.47/0.69      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.69        | (m1_subset_1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['41', '47'])).
% 0.47/0.69  thf('49', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf('50', plain,
% 0.47/0.69      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.69  thf('51', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('52', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.69  thf(t3_subset, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.69  thf('53', plain,
% 0.47/0.69      (![X3 : $i, X4 : $i]:
% 0.47/0.69         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.69  thf('54', plain,
% 0.47/0.69      ((r1_tarski @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.69  thf('56', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.69          | ~ (r2_hidden @ X18 @ X21)
% 0.47/0.69          | ~ (r1_tarski @ X21 @ X20)
% 0.47/0.69          | ~ (v3_pre_topc @ X21 @ X19)
% 0.47/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (l1_pre_topc @ X19)
% 0.47/0.69          | ~ (v2_pre_topc @ X19)
% 0.47/0.69          | (v2_struct_0 @ X19))),
% 0.47/0.69      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.69  thf('57', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69          | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | (m1_connsp_2 @ X0 @ sk_C_1 @ X1)
% 0.47/0.69          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69               sk_C_1)
% 0.47/0.69          | ~ (r1_tarski @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.69  thf('58', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('59', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('60', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.47/0.69  thf('61', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['21', '29'])).
% 0.47/0.69  thf('62', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.69          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.69          | (v3_pre_topc @ (sk_D @ X20 @ X18 @ X19) @ X19)
% 0.47/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (l1_pre_topc @ X19)
% 0.47/0.69          | ~ (v2_pre_topc @ X19)
% 0.47/0.69          | (v2_struct_0 @ X19))),
% 0.47/0.69      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69          | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.69          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ X0 @ sk_C_1) @ 
% 0.47/0.69             sk_C_1)
% 0.47/0.69          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.69  thf('64', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('65', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('66', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ X0 @ sk_C_1) @ 
% 0.47/0.69             sk_C_1)
% 0.47/0.69          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.47/0.69  thf('67', plain,
% 0.47/0.69      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.69        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69           sk_C_1)
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['60', '66'])).
% 0.47/0.69  thf('68', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf('69', plain,
% 0.47/0.69      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ sk_C_1)
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.69  thf('70', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('71', plain,
% 0.47/0.69      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ sk_C_1)),
% 0.47/0.69      inference('clc', [status(thm)], ['69', '70'])).
% 0.47/0.69  thf('72', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_C_1)
% 0.47/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | (m1_connsp_2 @ X0 @ sk_C_1 @ X1)
% 0.47/0.69          | ~ (r1_tarski @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1) @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['57', '58', '59', '71'])).
% 0.47/0.69  thf('73', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.69          | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.47/0.69               (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69          | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['54', '72'])).
% 0.47/0.69  thf(d10_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.69  thf('74', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.69  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.69      inference('simplify', [status(thm)], ['74'])).
% 0.47/0.69  thf('76', plain,
% 0.47/0.69      (![X3 : $i, X5 : $i]:
% 0.47/0.69         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.47/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.69  thf('77', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.69  thf('78', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.47/0.69          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_F @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.69          | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ X0)
% 0.47/0.69          | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['73', '77'])).
% 0.47/0.69  thf('79', plain,
% 0.47/0.69      (((v2_struct_0 @ sk_C_1)
% 0.47/0.69        | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.47/0.69        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['40', '78'])).
% 0.47/0.69  thf('80', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf('81', plain,
% 0.47/0.69      (((v2_struct_0 @ sk_C_1)
% 0.47/0.69        | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ sk_F))),
% 0.47/0.69      inference('demod', [status(thm)], ['79', '80'])).
% 0.47/0.69  thf('82', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('83', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.69      inference('clc', [status(thm)], ['81', '82'])).
% 0.47/0.69  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.69  thf('85', plain,
% 0.47/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.69         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.69          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.69          | (m1_subset_1 @ (sk_D @ X20 @ X18 @ X19) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.69          | ~ (l1_pre_topc @ X19)
% 0.47/0.69          | ~ (v2_pre_topc @ X19)
% 0.47/0.69          | (v2_struct_0 @ X19))),
% 0.47/0.69      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.69  thf('86', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((v2_struct_0 @ X0)
% 0.47/0.69          | ~ (v2_pre_topc @ X0)
% 0.47/0.69          | ~ (l1_pre_topc @ X0)
% 0.47/0.69          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X1 @ X0) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.69          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 0.47/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.69  thf('87', plain,
% 0.47/0.69      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.69        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69        | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.69        | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['83', '86'])).
% 0.47/0.69  thf('88', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf('89', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('90', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.69  thf('91', plain,
% 0.47/0.69      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.47/0.69        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.47/0.69  thf('92', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('93', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.69      inference('clc', [status(thm)], ['91', '92'])).
% 0.47/0.69  thf(t39_pre_topc, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( l1_pre_topc @ A ) =>
% 0.47/0.69       ( ![B:$i]:
% 0.47/0.69         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.69           ( ![C:$i]:
% 0.47/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.69               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.47/0.69  thf('94', plain,
% 0.47/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.69         (~ (m1_pre_topc @ X10 @ X11)
% 0.47/0.69          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.47/0.69          | ~ (l1_pre_topc @ X11))),
% 0.47/0.69      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.47/0.69  thf('95', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (l1_pre_topc @ X0)
% 0.47/0.69          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.69          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.69  thf('96', plain,
% 0.47/0.69      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.69        | ~ (l1_pre_topc @ sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '95'])).
% 0.47/0.69  thf('97', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('98', plain,
% 0.47/0.69      (![X8 : $i, X9 : $i]:
% 0.47/0.69         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.69  thf('99', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['97', '98'])).
% 0.47/0.69  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('101', plain, ((l1_pre_topc @ sk_D_1)),
% 0.47/0.69      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.69  thf('102', plain,
% 0.47/0.69      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.47/0.69      inference('demod', [status(thm)], ['96', '101'])).
% 0.47/0.69  thf('103', plain,
% 0.47/0.69      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)
% 0.47/0.69        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('104', plain,
% 0.47/0.69      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.47/0.69      inference('split', [status(esa)], ['103'])).
% 0.47/0.69  thf('105', plain, (((sk_F) = (sk_G))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('106', plain,
% 0.47/0.69      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.47/0.69      inference('demod', [status(thm)], ['104', '105'])).
% 0.47/0.69  thf('107', plain,
% 0.47/0.69      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)
% 0.47/0.69        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('108', plain,
% 0.47/0.69      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)) | 
% 0.47/0.69       ~
% 0.47/0.69       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))),
% 0.47/0.69      inference('split', [status(esa)], ['107'])).
% 0.47/0.69  thf('109', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('110', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.69  thf('111', plain,
% 0.47/0.69      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('split', [status(esa)], ['103'])).
% 0.47/0.69  thf('112', plain,
% 0.47/0.69      ((m1_subset_1 @ sk_E @ 
% 0.47/0.69        (k1_zfmisc_1 @ 
% 0.47/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t81_tmap_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.69       ( ![B:$i]:
% 0.47/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.69             ( l1_pre_topc @ B ) ) =>
% 0.47/0.69           ( ![C:$i]:
% 0.47/0.69             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.69               ( ![D:$i]:
% 0.47/0.69                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.69                   ( ![E:$i]:
% 0.47/0.69                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.69                         ( v1_funct_2 @
% 0.47/0.69                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.69                         ( m1_subset_1 @
% 0.47/0.69                           E @ 
% 0.47/0.69                           ( k1_zfmisc_1 @
% 0.47/0.69                             ( k2_zfmisc_1 @
% 0.47/0.69                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.69                       ( ![F:$i]:
% 0.47/0.69                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.69                           ( ![G:$i]:
% 0.47/0.69                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.69                               ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.69                                   ( m1_pre_topc @ D @ C ) & 
% 0.47/0.69                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.47/0.69                                 ( r1_tmap_1 @
% 0.47/0.69                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.47/0.69                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.69  thf('113', plain,
% 0.47/0.69      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.69         ((v2_struct_0 @ X30)
% 0.47/0.69          | ~ (v2_pre_topc @ X30)
% 0.47/0.69          | ~ (l1_pre_topc @ X30)
% 0.47/0.69          | (v2_struct_0 @ X31)
% 0.47/0.69          | ~ (m1_pre_topc @ X31 @ X32)
% 0.47/0.69          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 0.47/0.69          | ~ (m1_pre_topc @ X31 @ X34)
% 0.47/0.69          | ~ (r1_tmap_1 @ X34 @ X30 @ X35 @ X33)
% 0.47/0.69          | ((X33) != (X36))
% 0.47/0.69          | (r1_tmap_1 @ X31 @ X30 @ 
% 0.47/0.69             (k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35) @ X36)
% 0.47/0.69          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.47/0.69          | ~ (m1_subset_1 @ X35 @ 
% 0.47/0.69               (k1_zfmisc_1 @ 
% 0.47/0.69                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))))
% 0.47/0.69          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))
% 0.47/0.69          | ~ (v1_funct_1 @ X35)
% 0.47/0.69          | ~ (m1_pre_topc @ X34 @ X32)
% 0.47/0.69          | (v2_struct_0 @ X34)
% 0.47/0.69          | ~ (l1_pre_topc @ X32)
% 0.47/0.69          | ~ (v2_pre_topc @ X32)
% 0.47/0.69          | (v2_struct_0 @ X32))),
% 0.47/0.69      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.47/0.69  thf('114', plain,
% 0.47/0.69      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.69         ((v2_struct_0 @ X32)
% 0.47/0.69          | ~ (v2_pre_topc @ X32)
% 0.47/0.69          | ~ (l1_pre_topc @ X32)
% 0.47/0.69          | (v2_struct_0 @ X34)
% 0.47/0.69          | ~ (m1_pre_topc @ X34 @ X32)
% 0.47/0.69          | ~ (v1_funct_1 @ X35)
% 0.47/0.69          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))
% 0.47/0.69          | ~ (m1_subset_1 @ X35 @ 
% 0.47/0.69               (k1_zfmisc_1 @ 
% 0.47/0.69                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))))
% 0.47/0.69          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.47/0.69          | (r1_tmap_1 @ X31 @ X30 @ 
% 0.47/0.69             (k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35) @ X36)
% 0.47/0.69          | ~ (r1_tmap_1 @ X34 @ X30 @ X35 @ X36)
% 0.47/0.69          | ~ (m1_pre_topc @ X31 @ X34)
% 0.47/0.69          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.47/0.69          | ~ (m1_pre_topc @ X31 @ X32)
% 0.47/0.69          | (v2_struct_0 @ X31)
% 0.47/0.69          | ~ (l1_pre_topc @ X30)
% 0.47/0.69          | ~ (v2_pre_topc @ X30)
% 0.47/0.69          | (v2_struct_0 @ X30))),
% 0.47/0.69      inference('simplify', [status(thm)], ['113'])).
% 0.47/0.69  thf('115', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_B)
% 0.47/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.69          | (v2_struct_0 @ X0)
% 0.47/0.69          | ~ (m1_pre_topc @ X0 @ X1)
% 0.47/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.47/0.69          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.47/0.69          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.47/0.69          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.69             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.47/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.47/0.69          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.47/0.69               (u1_struct_0 @ sk_B))
% 0.47/0.69          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.69          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.47/0.69          | (v2_struct_0 @ sk_D_1)
% 0.47/0.69          | ~ (l1_pre_topc @ X1)
% 0.47/0.69          | ~ (v2_pre_topc @ X1)
% 0.47/0.69          | (v2_struct_0 @ X1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['112', '114'])).
% 0.47/0.69  thf('116', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('118', plain,
% 0.47/0.69      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('119', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('120', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((v2_struct_0 @ sk_B)
% 0.47/0.69          | (v2_struct_0 @ X0)
% 0.47/0.69          | ~ (m1_pre_topc @ X0 @ X1)
% 0.47/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.47/0.69          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.47/0.69          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.47/0.69          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.69             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.47/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.47/0.69          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.47/0.69          | (v2_struct_0 @ sk_D_1)
% 0.47/0.69          | ~ (l1_pre_topc @ X1)
% 0.47/0.69          | ~ (v2_pre_topc @ X1)
% 0.47/0.69          | (v2_struct_0 @ X1))),
% 0.47/0.69      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.47/0.69  thf('121', plain,
% 0.47/0.69      ((![X0 : $i, X1 : $i]:
% 0.47/0.69          ((v2_struct_0 @ X0)
% 0.47/0.69           | ~ (v2_pre_topc @ X0)
% 0.47/0.69           | ~ (l1_pre_topc @ X0)
% 0.47/0.69           | (v2_struct_0 @ sk_D_1)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.47/0.69           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.47/0.69           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.69              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.47/0.69           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.47/0.69           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.47/0.69           | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.69           | (v2_struct_0 @ X1)
% 0.47/0.69           | (v2_struct_0 @ sk_B)))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['111', '120'])).
% 0.47/0.69  thf('122', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('123', plain,
% 0.47/0.69      ((![X0 : $i, X1 : $i]:
% 0.47/0.69          ((v2_struct_0 @ X0)
% 0.47/0.69           | ~ (v2_pre_topc @ X0)
% 0.47/0.69           | ~ (l1_pre_topc @ X0)
% 0.47/0.69           | (v2_struct_0 @ sk_D_1)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.47/0.69           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.47/0.69           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.69              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.47/0.69           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.47/0.69           | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.69           | (v2_struct_0 @ X1)
% 0.47/0.69           | (v2_struct_0 @ sk_B)))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('demod', [status(thm)], ['121', '122'])).
% 0.47/0.69  thf('124', plain,
% 0.47/0.69      ((![X0 : $i]:
% 0.47/0.69          ((v2_struct_0 @ sk_B)
% 0.47/0.69           | (v2_struct_0 @ sk_C_1)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.47/0.69           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.47/0.69           | (v2_struct_0 @ sk_D_1)
% 0.47/0.69           | ~ (l1_pre_topc @ X0)
% 0.47/0.69           | ~ (v2_pre_topc @ X0)
% 0.47/0.69           | (v2_struct_0 @ X0)))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['110', '123'])).
% 0.47/0.69  thf('125', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('126', plain,
% 0.47/0.69      ((![X0 : $i]:
% 0.47/0.69          ((v2_struct_0 @ sk_B)
% 0.47/0.69           | (v2_struct_0 @ sk_C_1)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.47/0.69           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.47/0.69           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.47/0.69           | (v2_struct_0 @ sk_D_1)
% 0.47/0.69           | ~ (l1_pre_topc @ X0)
% 0.47/0.69           | ~ (v2_pre_topc @ X0)
% 0.47/0.69           | (v2_struct_0 @ X0)))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('demod', [status(thm)], ['124', '125'])).
% 0.47/0.69  thf('127', plain,
% 0.47/0.69      ((((v2_struct_0 @ sk_A)
% 0.47/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.69         | (v2_struct_0 @ sk_D_1)
% 0.47/0.69         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.47/0.69         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.47/0.69         | (v2_struct_0 @ sk_C_1)
% 0.47/0.69         | (v2_struct_0 @ sk_B)))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['109', '126'])).
% 0.47/0.69  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('130', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('131', plain,
% 0.47/0.69      ((((v2_struct_0 @ sk_A)
% 0.47/0.69         | (v2_struct_0 @ sk_D_1)
% 0.47/0.69         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.47/0.69         | (v2_struct_0 @ sk_C_1)
% 0.47/0.69         | (v2_struct_0 @ sk_B)))
% 0.47/0.69         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.47/0.69  thf('132', plain,
% 0.47/0.69      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))
% 0.47/0.69         <= (~
% 0.47/0.69             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.47/0.69      inference('split', [status(esa)], ['107'])).
% 0.47/0.69  thf('133', plain, (((sk_F) = (sk_G))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('134', plain,
% 0.47/0.69      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F))
% 0.47/0.69         <= (~
% 0.47/0.69             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.47/0.69      inference('demod', [status(thm)], ['132', '133'])).
% 0.47/0.69  thf('135', plain,
% 0.47/0.69      ((((v2_struct_0 @ sk_B)
% 0.47/0.69         | (v2_struct_0 @ sk_C_1)
% 0.47/0.69         | (v2_struct_0 @ sk_D_1)
% 0.47/0.69         | (v2_struct_0 @ sk_A)))
% 0.47/0.69         <= (~
% 0.47/0.69             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.47/0.69             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['131', '134'])).
% 0.47/0.69  thf('136', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('137', plain,
% 0.47/0.69      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.47/0.69         <= (~
% 0.47/0.69             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.47/0.69             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['135', '136'])).
% 0.47/0.69  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('139', plain,
% 0.47/0.69      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.47/0.69         <= (~
% 0.47/0.69             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.69               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.47/0.69             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.69      inference('clc', [status(thm)], ['137', '138'])).
% 0.47/0.69  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('141', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_C_1))
% 0.47/0.70         <= (~
% 0.47/0.70             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.70               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.47/0.70             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.70      inference('clc', [status(thm)], ['139', '140'])).
% 0.47/0.70  thf('142', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('143', plain,
% 0.47/0.70      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.70         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.47/0.70       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.47/0.70      inference('sup-', [status(thm)], ['141', '142'])).
% 0.47/0.70  thf('144', plain,
% 0.47/0.70      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.70         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.47/0.70       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.47/0.70      inference('split', [status(esa)], ['103'])).
% 0.47/0.70  thf('145', plain,
% 0.47/0.70      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.70         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['108', '143', '144'])).
% 0.47/0.70  thf('146', plain,
% 0.47/0.70      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.70        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['106', '145'])).
% 0.47/0.70  thf('147', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t84_tmap_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.70             ( l1_pre_topc @ B ) ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.70               ( ![D:$i]:
% 0.47/0.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.70                   ( ![E:$i]:
% 0.47/0.70                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.70                         ( v1_funct_2 @
% 0.47/0.70                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.70                         ( m1_subset_1 @
% 0.47/0.70                           E @ 
% 0.47/0.70                           ( k1_zfmisc_1 @
% 0.47/0.70                             ( k2_zfmisc_1 @
% 0.47/0.70                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.70                       ( ( m1_pre_topc @ C @ D ) =>
% 0.47/0.70                         ( ![F:$i]:
% 0.47/0.70                           ( ( m1_subset_1 @
% 0.47/0.70                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.47/0.70                             ( ![G:$i]:
% 0.47/0.70                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.70                                 ( ![H:$i]:
% 0.47/0.70                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.70                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.47/0.70                                         ( r2_hidden @ G @ F ) & 
% 0.47/0.70                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.47/0.70                                         ( ( G ) = ( H ) ) ) =>
% 0.47/0.70                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.47/0.70                                         ( r1_tmap_1 @
% 0.47/0.70                                           C @ B @ 
% 0.47/0.70                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.47/0.70                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('148', plain,
% 0.47/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.47/0.70         X44 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X37)
% 0.47/0.70          | ~ (v2_pre_topc @ X37)
% 0.47/0.70          | ~ (l1_pre_topc @ X37)
% 0.47/0.70          | (v2_struct_0 @ X38)
% 0.47/0.70          | ~ (m1_pre_topc @ X38 @ X39)
% 0.47/0.70          | ~ (m1_pre_topc @ X40 @ X38)
% 0.47/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.47/0.70          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 0.47/0.70          | ~ (r1_tmap_1 @ X40 @ X37 @ 
% 0.47/0.70               (k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43) @ X42)
% 0.47/0.70          | (r1_tmap_1 @ X38 @ X37 @ X43 @ X44)
% 0.47/0.70          | ((X44) != (X42))
% 0.47/0.70          | ~ (r1_tarski @ X41 @ (u1_struct_0 @ X40))
% 0.47/0.70          | ~ (r2_hidden @ X44 @ X41)
% 0.47/0.70          | ~ (v3_pre_topc @ X41 @ X38)
% 0.47/0.70          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X38))
% 0.47/0.70          | ~ (m1_subset_1 @ X43 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 0.47/0.70          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))
% 0.47/0.70          | ~ (v1_funct_1 @ X43)
% 0.47/0.70          | ~ (m1_pre_topc @ X40 @ X39)
% 0.47/0.70          | (v2_struct_0 @ X40)
% 0.47/0.70          | ~ (l1_pre_topc @ X39)
% 0.47/0.70          | ~ (v2_pre_topc @ X39)
% 0.47/0.70          | (v2_struct_0 @ X39))),
% 0.47/0.70      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.47/0.70  thf('149', plain,
% 0.47/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X39)
% 0.47/0.70          | ~ (v2_pre_topc @ X39)
% 0.47/0.70          | ~ (l1_pre_topc @ X39)
% 0.47/0.70          | (v2_struct_0 @ X40)
% 0.47/0.70          | ~ (m1_pre_topc @ X40 @ X39)
% 0.47/0.70          | ~ (v1_funct_1 @ X43)
% 0.47/0.70          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))
% 0.47/0.70          | ~ (m1_subset_1 @ X43 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 0.47/0.70          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X38))
% 0.47/0.70          | ~ (v3_pre_topc @ X41 @ X38)
% 0.47/0.70          | ~ (r2_hidden @ X42 @ X41)
% 0.47/0.70          | ~ (r1_tarski @ X41 @ (u1_struct_0 @ X40))
% 0.47/0.70          | (r1_tmap_1 @ X38 @ X37 @ X43 @ X42)
% 0.47/0.70          | ~ (r1_tmap_1 @ X40 @ X37 @ 
% 0.47/0.70               (k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43) @ X42)
% 0.47/0.70          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 0.47/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.47/0.70          | ~ (m1_pre_topc @ X40 @ X38)
% 0.47/0.70          | ~ (m1_pre_topc @ X38 @ X39)
% 0.47/0.70          | (v2_struct_0 @ X38)
% 0.47/0.70          | ~ (l1_pre_topc @ X37)
% 0.47/0.70          | ~ (v2_pre_topc @ X37)
% 0.47/0.70          | (v2_struct_0 @ X37))),
% 0.47/0.70      inference('simplify', [status(thm)], ['148'])).
% 0.47/0.70  thf('150', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ sk_D_1)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.70          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.70          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.70               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.47/0.70          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.47/0.70          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.70          | ~ (r2_hidden @ X3 @ X2)
% 0.47/0.70          | ~ (v3_pre_topc @ X2 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.47/0.70          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.47/0.70               (u1_struct_0 @ sk_B))
% 0.47/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | (v2_struct_0 @ X1)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['147', '149'])).
% 0.47/0.70  thf('151', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('152', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('153', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('154', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('155', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ sk_D_1)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.70          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.70          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.70               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.47/0.70          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.47/0.70          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.70          | ~ (r2_hidden @ X3 @ X2)
% 0.47/0.70          | ~ (v3_pre_topc @ X2 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | (v2_struct_0 @ X1)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 0.47/0.70  thf('156', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_A)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.70          | (v2_struct_0 @ sk_C_1)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.47/0.70          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.47/0.70          | ~ (v3_pre_topc @ X0 @ sk_D_1)
% 0.47/0.70          | ~ (r2_hidden @ sk_F @ X0)
% 0.47/0.70          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.47/0.70          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.47/0.70          | (v2_struct_0 @ sk_D_1)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['146', '155'])).
% 0.47/0.70  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('159', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('160', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('161', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf('162', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('163', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('164', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_A)
% 0.47/0.70          | (v2_struct_0 @ sk_C_1)
% 0.47/0.70          | ~ (v3_pre_topc @ X0 @ sk_D_1)
% 0.47/0.70          | ~ (r2_hidden @ sk_F @ X0)
% 0.47/0.70          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.70          | (v2_struct_0 @ sk_D_1)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['156', '157', '158', '159', '160', '161', '162', '163'])).
% 0.47/0.70  thf('165', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | (v2_struct_0 @ sk_D_1)
% 0.47/0.70        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.47/0.70        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             (u1_struct_0 @ sk_C_1))
% 0.47/0.70        | ~ (r2_hidden @ sk_F @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.70        | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             sk_D_1)
% 0.47/0.70        | (v2_struct_0 @ sk_C_1)
% 0.47/0.70        | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['102', '164'])).
% 0.47/0.70  thf('166', plain,
% 0.47/0.70      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.70      inference('clc', [status(thm)], ['91', '92'])).
% 0.47/0.70  thf('167', plain,
% 0.47/0.70      (![X3 : $i, X4 : $i]:
% 0.47/0.70         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.70  thf('168', plain,
% 0.47/0.70      ((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70        (u1_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['166', '167'])).
% 0.47/0.70  thf('169', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.70      inference('clc', [status(thm)], ['81', '82'])).
% 0.47/0.70  thf('170', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.70  thf('171', plain,
% 0.47/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.70          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.70          | (r2_hidden @ X18 @ (sk_D @ X20 @ X18 @ X19))
% 0.47/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.70          | ~ (l1_pre_topc @ X19)
% 0.47/0.70          | ~ (v2_pre_topc @ X19)
% 0.47/0.70          | (v2_struct_0 @ X19))),
% 0.47/0.70      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.70  thf('172', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (r2_hidden @ X1 @ (sk_D @ (u1_struct_0 @ X0) @ X1 @ X0))
% 0.47/0.70          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['170', '171'])).
% 0.47/0.70  thf('173', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70        | (r2_hidden @ sk_F @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.70        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['169', '172'])).
% 0.47/0.70  thf('174', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf('175', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.70  thf('176', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.70  thf('177', plain,
% 0.47/0.70      (((r2_hidden @ sk_F @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1))
% 0.47/0.70        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 0.47/0.70  thf('178', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('179', plain,
% 0.47/0.70      ((r2_hidden @ sk_F @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1))),
% 0.47/0.70      inference('clc', [status(thm)], ['177', '178'])).
% 0.47/0.70  thf('180', plain,
% 0.47/0.70      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.47/0.70      inference('clc', [status(thm)], ['91', '92'])).
% 0.47/0.70  thf('181', plain,
% 0.47/0.70      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['96', '101'])).
% 0.47/0.70  thf('182', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t1_tsep_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.70           ( m1_subset_1 @
% 0.47/0.70             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('183', plain,
% 0.47/0.70      (![X25 : $i, X26 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X25 @ X26)
% 0.47/0.70          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.47/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.70          | ~ (l1_pre_topc @ X26))),
% 0.47/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.47/0.70  thf('184', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_D_1)
% 0.47/0.70        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['182', '183'])).
% 0.47/0.70  thf('185', plain, ((l1_pre_topc @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.70  thf('186', plain,
% 0.47/0.70      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.47/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['184', '185'])).
% 0.47/0.70  thf(t9_tsep_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70               ( ![D:$i]:
% 0.47/0.70                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70                   ( ![E:$i]:
% 0.47/0.70                     ( ( m1_subset_1 @
% 0.47/0.70                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.70                       ( ( ( v3_pre_topc @ C @ A ) & 
% 0.47/0.70                           ( r1_tarski @ C @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.70                           ( r1_tarski @ D @ C ) & ( ( D ) = ( E ) ) ) =>
% 0.47/0.70                         ( ( v3_pre_topc @ E @ B ) <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('187', plain,
% 0.47/0.70      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X45 @ X46)
% 0.47/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.47/0.70          | ~ (v3_pre_topc @ X48 @ X46)
% 0.47/0.70          | ~ (r1_tarski @ X48 @ (u1_struct_0 @ X45))
% 0.47/0.70          | ~ (r1_tarski @ X47 @ X48)
% 0.47/0.70          | ((X47) != (X49))
% 0.47/0.70          | ~ (v3_pre_topc @ X49 @ X45)
% 0.47/0.70          | (v3_pre_topc @ X47 @ X46)
% 0.47/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.47/0.70          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.47/0.70          | ~ (l1_pre_topc @ X46)
% 0.47/0.70          | ~ (v2_pre_topc @ X46))),
% 0.47/0.70      inference('cnf', [status(esa)], [t9_tsep_1])).
% 0.47/0.70  thf('188', plain,
% 0.47/0.70      (![X45 : $i, X46 : $i, X48 : $i, X49 : $i]:
% 0.47/0.70         (~ (v2_pre_topc @ X46)
% 0.47/0.70          | ~ (l1_pre_topc @ X46)
% 0.47/0.70          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.47/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.47/0.70          | (v3_pre_topc @ X49 @ X46)
% 0.47/0.70          | ~ (v3_pre_topc @ X49 @ X45)
% 0.47/0.70          | ~ (r1_tarski @ X49 @ X48)
% 0.47/0.70          | ~ (r1_tarski @ X48 @ (u1_struct_0 @ X45))
% 0.47/0.70          | ~ (v3_pre_topc @ X48 @ X46)
% 0.47/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.47/0.70          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.47/0.70      inference('simplify', [status(thm)], ['187'])).
% 0.47/0.70  thf('189', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)
% 0.47/0.70          | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70          | ~ (v3_pre_topc @ X1 @ X0)
% 0.47/0.70          | (v3_pre_topc @ X1 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ sk_D_1)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_D_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['186', '188'])).
% 0.47/0.70  thf('190', plain,
% 0.47/0.70      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.47/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['184', '185'])).
% 0.47/0.70  thf(t16_tsep_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.47/0.70                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.47/0.70                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('191', plain,
% 0.47/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X22 @ X23)
% 0.47/0.70          | ((X24) != (u1_struct_0 @ X22))
% 0.47/0.70          | ~ (v1_tsep_1 @ X22 @ X23)
% 0.47/0.70          | ~ (m1_pre_topc @ X22 @ X23)
% 0.47/0.70          | (v3_pre_topc @ X24 @ X23)
% 0.47/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.47/0.70          | ~ (l1_pre_topc @ X23)
% 0.47/0.70          | ~ (v2_pre_topc @ X23))),
% 0.47/0.70      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.47/0.70  thf('192', plain,
% 0.47/0.70      (![X22 : $i, X23 : $i]:
% 0.47/0.70         (~ (v2_pre_topc @ X23)
% 0.47/0.70          | ~ (l1_pre_topc @ X23)
% 0.47/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.47/0.70          | (v3_pre_topc @ (u1_struct_0 @ X22) @ X23)
% 0.47/0.70          | ~ (v1_tsep_1 @ X22 @ X23)
% 0.47/0.70          | ~ (m1_pre_topc @ X22 @ X23))),
% 0.47/0.70      inference('simplify', [status(thm)], ['191'])).
% 0.47/0.70  thf('193', plain,
% 0.47/0.70      ((~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.47/0.70        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.47/0.70        | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_D_1)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_D_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['190', '192'])).
% 0.47/0.70  thf('194', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('195', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('196', plain, ((l1_pre_topc @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.70  thf('197', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('198', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X6 @ X7)
% 0.47/0.70          | (v2_pre_topc @ X6)
% 0.47/0.70          | ~ (l1_pre_topc @ X7)
% 0.47/0.70          | ~ (v2_pre_topc @ X7))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.70  thf('199', plain,
% 0.47/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.70        | (v2_pre_topc @ sk_D_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['197', '198'])).
% 0.47/0.70  thf('200', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('202', plain, ((v2_pre_topc @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['199', '200', '201'])).
% 0.47/0.70  thf('203', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['193', '194', '195', '196', '202'])).
% 0.47/0.70  thf('204', plain, ((l1_pre_topc @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['99', '100'])).
% 0.47/0.70  thf('205', plain, ((v2_pre_topc @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['199', '200', '201'])).
% 0.47/0.70  thf('206', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.47/0.70          | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70          | ~ (v3_pre_topc @ X1 @ X0)
% 0.47/0.70          | (v3_pre_topc @ X1 @ sk_D_1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.70      inference('demod', [status(thm)], ['189', '203', '204', '205'])).
% 0.47/0.70  thf('207', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.70          | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             sk_D_1)
% 0.47/0.70          | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70               X0)
% 0.47/0.70          | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70               (u1_struct_0 @ sk_C_1))
% 0.47/0.70          | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ sk_D_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['181', '206'])).
% 0.47/0.70  thf('208', plain,
% 0.47/0.70      ((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70        (u1_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['166', '167'])).
% 0.47/0.70  thf('209', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.70          | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             sk_D_1)
% 0.47/0.70          | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70               X0)
% 0.47/0.70          | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ sk_D_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['207', '208'])).
% 0.47/0.70  thf('210', plain,
% 0.47/0.70      ((~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.47/0.70        | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70        | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70             sk_C_1)
% 0.47/0.70        | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70           sk_D_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['180', '209'])).
% 0.47/0.70  thf('211', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('212', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.70      inference('simplify', [status(thm)], ['74'])).
% 0.47/0.70  thf('213', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.47/0.70      inference('clc', [status(thm)], ['81', '82'])).
% 0.47/0.70  thf('214', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.70  thf('215', plain,
% 0.47/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.47/0.70          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.47/0.70          | (v3_pre_topc @ (sk_D @ X20 @ X18 @ X19) @ X19)
% 0.47/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.70          | ~ (l1_pre_topc @ X19)
% 0.47/0.70          | ~ (v2_pre_topc @ X19)
% 0.47/0.70          | (v2_struct_0 @ X19))),
% 0.47/0.70      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.47/0.70  thf('216', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ X0) @ X1 @ X0) @ X0)
% 0.47/0.70          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['214', '215'])).
% 0.47/0.70  thf('217', plain,
% 0.47/0.70      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.47/0.70        | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ 
% 0.47/0.70           sk_C_1)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C_1)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_C_1)
% 0.47/0.70        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['213', '216'])).
% 0.47/0.70  thf('218', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf('219', plain, ((l1_pre_topc @ sk_C_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.70  thf('220', plain, ((v2_pre_topc @ sk_C_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.70  thf('221', plain,
% 0.47/0.70      (((v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ sk_C_1)
% 0.47/0.70        | (v2_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 0.47/0.70  thf('222', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('223', plain,
% 0.47/0.70      ((v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ sk_C_1)),
% 0.47/0.70      inference('clc', [status(thm)], ['221', '222'])).
% 0.47/0.70  thf('224', plain,
% 0.47/0.70      ((v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_C_1) @ sk_F @ sk_C_1) @ sk_D_1)),
% 0.47/0.70      inference('demod', [status(thm)], ['210', '211', '212', '223'])).
% 0.47/0.70  thf('225', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | (v2_struct_0 @ sk_D_1)
% 0.47/0.70        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.47/0.70        | (v2_struct_0 @ sk_C_1)
% 0.47/0.70        | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['165', '168', '179', '224'])).
% 0.47/0.70  thf('226', plain,
% 0.47/0.70      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.47/0.70         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.47/0.70      inference('split', [status(esa)], ['107'])).
% 0.47/0.70  thf('227', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['108', '143'])).
% 0.47/0.70  thf('228', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['226', '227'])).
% 0.47/0.70  thf('229', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_A)
% 0.47/0.70        | (v2_struct_0 @ sk_C_1)
% 0.47/0.70        | (v2_struct_0 @ sk_D_1)
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['225', '228'])).
% 0.47/0.70  thf('230', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('231', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['229', '230'])).
% 0.47/0.70  thf('232', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('233', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.47/0.70      inference('clc', [status(thm)], ['231', '232'])).
% 0.47/0.70  thf('234', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('235', plain, ((v2_struct_0 @ sk_C_1)),
% 0.47/0.70      inference('clc', [status(thm)], ['233', '234'])).
% 0.47/0.70  thf('236', plain, ($false), inference('demod', [status(thm)], ['0', '235'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
