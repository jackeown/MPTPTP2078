%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1711+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N5USMUpdv7

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:07 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  260 (2583 expanded)
%              Number of leaves         :   31 ( 734 expanded)
%              Depth                    :   26
%              Number of atoms          : 3096 (84923 expanded)
%              Number of equality atoms :   10 (2357 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_1_type,type,(
    sk_G_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t20_tmap_1,conjecture,(
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
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ( ( ( E = D )
                              & ( F = D ) )
                           => ! [G: $i] :
                                ( ( m1_connsp_2 @ G @ B @ E )
                               => ! [H: $i] :
                                    ( ( m1_connsp_2 @ H @ C @ F )
                                   => ? [I: $i] :
                                        ( ( r1_tarski @ I @ ( k2_xboole_0 @ G @ H ) )
                                        & ( r2_hidden @ D @ I )
                                        & ( v3_pre_topc @ I @ ( k1_tsep_1 @ A @ B @ C ) )
                                        & ( m1_subset_1 @ I @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                           => ( ( ( E = D )
                                & ( F = D ) )
                             => ! [G: $i] :
                                  ( ( m1_connsp_2 @ G @ B @ E )
                                 => ! [H: $i] :
                                      ( ( m1_connsp_2 @ H @ C @ F )
                                     => ? [I: $i] :
                                          ( ( r1_tarski @ I @ ( k2_xboole_0 @ G @ H ) )
                                          & ( r2_hidden @ D @ I )
                                          & ( v3_pre_topc @ I @ ( k1_tsep_1 @ A @ B @ C ) )
                                          & ( m1_subset_1 @ I @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_E = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_E = sk_F ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['1','4'])).

thf('7',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_E = sk_F ),
    inference('sup+',[status(thm)],['2','3'])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_connsp_2 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','17','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

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

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ sk_H @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ sk_H @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_connsp_2 @ sk_G_1 @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_connsp_2 @ sk_G_1 @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_connsp_2 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','47','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_G_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_E = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t19_tmap_1,axiom,(
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
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                         => ~ ( ( v3_pre_topc @ E @ B )
                              & ( r2_hidden @ D @ E )
                              & ( v3_pre_topc @ F @ C )
                              & ( r2_hidden @ D @ F )
                              & ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) )
                                 => ~ ( ( v3_pre_topc @ G @ ( k1_tsep_1 @ A @ B @ C ) )
                                      & ( r2_hidden @ D @ G )
                                      & ( r1_tarski @ G @ ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ X13 @ ( sk_G @ X15 @ X16 @ X13 @ X14 @ X11 @ X12 ) )
      | ~ ( v3_pre_topc @ X16 @ X11 )
      | ~ ( r2_hidden @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_tmap_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( r2_hidden @ sk_E @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( r2_hidden @ sk_E @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( r2_hidden @ sk_E @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,(
    m1_connsp_2 @ sk_G_1 @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_G_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('80',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( v3_pre_topc @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_connsp_2 @ sk_G_1 @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_G_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('92',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( sk_D @ X22 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( r2_hidden @ sk_E @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','89','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) )
    | ~ ( v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','102'])).

thf('104',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['1','4'])).

thf('105',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('106',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( sk_D @ X22 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_H @ X0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('109',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_H @ X0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('113',plain,
    ( ( r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['1','4'])).

thf('117',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('118',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( v3_pre_topc @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v3_pre_topc @ ( sk_D @ sk_H @ X0 @ sk_C ) @ sk_C )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('121',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v3_pre_topc @ ( sk_D @ sk_H @ X0 @ sk_C ) @ sk_C )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ( v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('125',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','115','127'])).

thf('129',plain,(
    m1_connsp_2 @ sk_H @ sk_C @ sk_E ),
    inference(demod,[status(thm)],['1','4'])).

thf('130',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('131',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r1_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( r1_tarski @ ( sk_D @ sk_H @ X0 @ sk_C ) @ sk_H )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('134',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_tarski @ ( sk_D @ sk_H @ X0 @ sk_C ) @ sk_H )
      | ~ ( m1_connsp_2 @ sk_H @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tarski @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_H )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('138',plain,
    ( ( r1_tarski @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_H )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r1_tarski @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_H ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    m1_connsp_2 @ sk_G_1 @ sk_B @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_G_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('143',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r1_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r1_tarski @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) @ sk_G_1 )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('146',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( sk_D @ sk_G_1 @ X0 @ sk_B ) @ sk_G_1 )
      | ~ ( m1_connsp_2 @ sk_G_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_G_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( r1_tarski @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_G_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    r1_tarski @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_G_1 ),
    inference(clc,[status(thm)],['150','151'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('153',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ X1 ) @ ( k2_xboole_0 @ sk_G_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( sk_D @ sk_H @ sk_E @ sk_C ) ) @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) ),
    inference('sup-',[status(thm)],['140','154'])).

thf('156',plain,(
    m1_subset_1 @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('157',plain,(
    m1_subset_1 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('158',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('159',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r1_tarski @ ( sk_G @ X15 @ X16 @ X13 @ X14 @ X11 @ X12 ) @ ( k2_xboole_0 @ X16 @ X15 ) )
      | ~ ( v3_pre_topc @ X16 @ X11 )
      | ~ ( r2_hidden @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_tmap_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162','163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( r1_tarski @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','165'])).

thf('167',plain,(
    v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('168',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( r1_tarski @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( sk_D @ sk_H @ sk_E @ sk_C ) ) )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) )
    | ~ ( v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','169'])).

thf('171',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('172',plain,(
    v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['125','126'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( sk_D @ sk_H @ sk_E @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('174',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( sk_D @ sk_H @ sk_E @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['155','175'])).

thf('177',plain,(
    m1_subset_1 @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('178',plain,(
    m1_subset_1 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('179',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('180',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( v3_pre_topc @ ( sk_G @ X15 @ X16 @ X13 @ X14 @ X11 @ X12 ) @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) )
      | ~ ( v3_pre_topc @ X16 @ X11 )
      | ~ ( r2_hidden @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_tmap_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( v3_pre_topc @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','186'])).

thf('188',plain,(
    v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('189',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( v3_pre_topc @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) )
    | ~ ( v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['177','190'])).

thf('192',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('193',plain,(
    v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['125','126'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
    m1_subset_1 @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('196',plain,(
    m1_subset_1 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('197',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('198',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( m1_subset_1 @ ( sk_G @ X15 @ X16 @ X13 @ X14 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X12 @ X11 @ X14 ) ) ) )
      | ~ ( v3_pre_topc @ X16 @ X11 )
      | ~ ( r2_hidden @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X12 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_tmap_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_G @ X1 @ X0 @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ~ ( r2_hidden @ sk_E @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( m1_subset_1 @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('206',plain,(
    v3_pre_topc @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('207',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ( m1_subset_1 @ ( sk_G @ X0 @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) )
    | ~ ( v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['195','208'])).

thf('210',plain,(
    r2_hidden @ sk_E @ ( sk_D @ sk_H @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('211',plain,(
    v3_pre_topc @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['125','126'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    ! [X24: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) )
      | ~ ( r2_hidden @ sk_D_1 @ X24 )
      | ~ ( v3_pre_topc @ X24 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    sk_E = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X24: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) )
      | ~ ( r2_hidden @ sk_E @ X24 )
      | ~ ( v3_pre_topc @ X24 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['212','215'])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) )
    | ~ ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['194','216'])).

thf('218',plain,
    ( ~ ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_G_1 @ sk_H ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','218'])).

thf('220',plain,
    ( ~ ( r2_hidden @ sk_E @ ( sk_G @ ( sk_D @ sk_H @ sk_E @ sk_C ) @ ( sk_D @ sk_G_1 @ sk_E @ sk_B ) @ sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','220'])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    $false ),
    inference(demod,[status(thm)],['0','226'])).


%------------------------------------------------------------------------------
