%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qsesGO5Op8

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 512 expanded)
%              Number of leaves         :   39 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          : 2311 (17563 expanded)
%              Number of equality atoms :   13 ( 229 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( m1_connsp_2 @ ( sk_C @ X19 @ X18 ) @ X18 @ X19 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_connsp_2 @ X17 @ X15 @ X16 ) ) ),
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

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_C_1 ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_F @ ( sk_C @ sk_F @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,
    ( ( r2_hidden @ sk_F @ ( sk_C @ sk_F @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ sk_F @ ( sk_C @ sk_F @ sk_C_1 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r1_tmap_1 @ X41 @ X38 @ ( k3_tmap_1 @ X40 @ X38 @ X39 @ X41 @ X44 ) @ X43 )
      | ( r1_tmap_1 @ X39 @ X38 @ X44 @ X45 )
      | ( X45 != X43 )
      | ~ ( r1_tarski @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r2_hidden @ X45 @ X42 )
      | ~ ( v3_pre_topc @ X42 @ X39 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('59',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X39 ) )
      | ~ ( v3_pre_topc @ X42 @ X39 )
      | ~ ( r2_hidden @ X43 @ X42 )
      | ~ ( r1_tarski @ X42 @ ( u1_struct_0 @ X41 ) )
      | ( r1_tmap_1 @ X39 @ X38 @ X44 @ X43 )
      | ~ ( r1_tmap_1 @ X41 @ X38 @ ( k3_tmap_1 @ X40 @ X38 @ X39 @ X41 @ X44 ) @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('72',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['52','74'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','51'])).

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

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('85',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('87',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['81','82','83','84','90'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['75','77','91'])).

thf('93',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['43','92'])).

thf('94',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_F @ sk_C_1 ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['40','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['53'])).

thf('110',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('112',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['53'])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X32 @ X35 )
      | ~ ( r1_tmap_1 @ X35 @ X31 @ X36 @ X34 )
      | ( X34 != X37 )
      | ( r1_tmap_1 @ X32 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X35 @ X32 @ X36 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('115',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X32 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X35 @ X32 @ X36 ) @ X37 )
      | ~ ( r1_tmap_1 @ X35 @ X31 @ X36 @ X37 )
      | ~ ( m1_pre_topc @ X32 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
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
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
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
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,
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
    inference('sup-',[status(thm)],['112','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
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
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
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
    inference('sup-',[status(thm)],['111','124'])).

thf('126',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
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
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['110','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','108','109','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qsesGO5Op8
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:02:15 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 151 iterations in 0.079s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(t86_tmap_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.54             ( l1_pre_topc @ B ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.54                   ( ![E:$i]:
% 0.20/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.54                         ( v1_funct_2 @
% 0.20/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                         ( m1_subset_1 @
% 0.20/0.54                           E @ 
% 0.20/0.54                           ( k1_zfmisc_1 @
% 0.20/0.54                             ( k2_zfmisc_1 @
% 0.20/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.54                         ( ![F:$i]:
% 0.20/0.54                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.54                             ( ![G:$i]:
% 0.20/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.54                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.54                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.54                                     ( r1_tmap_1 @
% 0.20/0.54                                       C @ B @ 
% 0.20/0.54                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.54                ( l1_pre_topc @ B ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.54                  ( ![D:$i]:
% 0.20/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.54                      ( ![E:$i]:
% 0.20/0.54                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.54                            ( v1_funct_2 @
% 0.20/0.54                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                            ( m1_subset_1 @
% 0.20/0.54                              E @ 
% 0.20/0.54                              ( k1_zfmisc_1 @
% 0.20/0.54                                ( k2_zfmisc_1 @
% 0.20/0.54                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.54                            ( ![F:$i]:
% 0.20/0.54                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.54                                ( ![G:$i]:
% 0.20/0.54                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.54                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.54                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.54                                        ( r1_tmap_1 @
% 0.20/0.54                                          C @ B @ 
% 0.20/0.54                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.20/0.54        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.20/0.54       ~
% 0.20/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('3', plain, (((sk_F) = (sk_G))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(existence_m1_connsp_2, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (v2_pre_topc @ X18)
% 0.20/0.54          | (v2_struct_0 @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.20/0.54          | (m1_connsp_2 @ (sk_C @ X19 @ X18) @ X18 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.20/0.54        | (v2_struct_0 @ sk_C_1)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.54          | (v2_pre_topc @ X11)
% 0.20/0.54          | ~ (l1_pre_topc @ X12)
% 0.20/0.54          | ~ (v2_pre_topc @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v2_pre_topc @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('12', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.54  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_m1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.54          | (l1_pre_topc @ X13)
% 0.20/0.54          | ~ (l1_pre_topc @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.54  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)
% 0.20/0.54        | (v2_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '12', '17'])).
% 0.20/0.54  thf('19', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.20/0.54      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ sk_F)),
% 0.20/0.54      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('22', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(dt_m1_connsp_2, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.20/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X15)
% 0.20/0.54          | ~ (v2_pre_topc @ X15)
% 0.20/0.54          | (v2_struct_0 @ X15)
% 0.20/0.54          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.54          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.54          | ~ (m1_connsp_2 @ X17 @ X15 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F)
% 0.20/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.54          | (v2_struct_0 @ sk_C_1)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.54  thf('26', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F)
% 0.20/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.54          | (v2_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.54  thf('28', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.54          | ~ (m1_connsp_2 @ X0 @ sk_C_1 @ sk_F))),
% 0.20/0.54      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '29'])).
% 0.20/0.54  thf(t6_connsp_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54          | ~ (m1_connsp_2 @ X20 @ X21 @ X22)
% 0.20/0.54          | (r2_hidden @ X22 @ X20)
% 0.20/0.54          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.20/0.54          | ~ (l1_pre_topc @ X21)
% 0.20/0.54          | ~ (v2_pre_topc @ X21)
% 0.20/0.54          | (v2_struct_0 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_C_1)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_C_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.54          | (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1))
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.54  thf('34', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_C_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.54          | (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1))
% 0.20/0.54          | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_C_1) @ sk_C_1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((r2_hidden @ sk_F @ (sk_C @ sk_F @ sk_C_1))
% 0.20/0.54        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.54        | (v2_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '35'])).
% 0.20/0.54  thf('37', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((r2_hidden @ sk_F @ (sk_C @ sk_F @ sk_C_1)) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain, ((r2_hidden @ sk_F @ (sk_C @ sk_F @ sk_C_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(t2_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((r2_hidden @ X3 @ X4)
% 0.20/0.54          | (v1_xboole_0 @ X4)
% 0.20/0.54          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.54        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t1_tsep_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( m1_subset_1 @
% 0.20/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.54          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.54          | ~ (l1_pre_topc @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.54  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.55          | (l1_pre_topc @ X13)
% 0.20/0.55          | ~ (l1_pre_topc @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('49', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.20/0.55        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('split', [status(esa)], ['53'])).
% 0.20/0.55  thf('55', plain, (((sk_F) = (sk_G))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t84_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.55                         ( ![F:$i]:
% 0.20/0.55                           ( ( m1_subset_1 @
% 0.20/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.55                             ( ![G:$i]:
% 0.20/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                                 ( ![H:$i]:
% 0.20/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.55                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.55                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.55                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.55                                         ( r1_tmap_1 @
% 0.20/0.55                                           C @ B @ 
% 0.20/0.55                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.20/0.55         X45 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X38)
% 0.20/0.55          | ~ (v2_pre_topc @ X38)
% 0.20/0.55          | ~ (l1_pre_topc @ X38)
% 0.20/0.55          | (v2_struct_0 @ X39)
% 0.20/0.55          | ~ (m1_pre_topc @ X39 @ X40)
% 0.20/0.55          | ~ (m1_pre_topc @ X41 @ X39)
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.20/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X41))
% 0.20/0.55          | ~ (r1_tmap_1 @ X41 @ X38 @ 
% 0.20/0.55               (k3_tmap_1 @ X40 @ X38 @ X39 @ X41 @ X44) @ X43)
% 0.20/0.55          | (r1_tmap_1 @ X39 @ X38 @ X44 @ X45)
% 0.20/0.55          | ((X45) != (X43))
% 0.20/0.55          | ~ (r1_tarski @ X42 @ (u1_struct_0 @ X41))
% 0.20/0.55          | ~ (r2_hidden @ X45 @ X42)
% 0.20/0.55          | ~ (v3_pre_topc @ X42 @ X39)
% 0.20/0.55          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X39))
% 0.20/0.55          | ~ (m1_subset_1 @ X44 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))))
% 0.20/0.55          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))
% 0.20/0.55          | ~ (v1_funct_1 @ X44)
% 0.20/0.55          | ~ (m1_pre_topc @ X41 @ X40)
% 0.20/0.55          | (v2_struct_0 @ X41)
% 0.20/0.55          | ~ (l1_pre_topc @ X40)
% 0.20/0.55          | ~ (v2_pre_topc @ X40)
% 0.20/0.55          | (v2_struct_0 @ X40))),
% 0.20/0.55      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X40)
% 0.20/0.55          | ~ (v2_pre_topc @ X40)
% 0.20/0.55          | ~ (l1_pre_topc @ X40)
% 0.20/0.55          | (v2_struct_0 @ X41)
% 0.20/0.55          | ~ (m1_pre_topc @ X41 @ X40)
% 0.20/0.55          | ~ (v1_funct_1 @ X44)
% 0.20/0.55          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))
% 0.20/0.55          | ~ (m1_subset_1 @ X44 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))))
% 0.20/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X39))
% 0.20/0.55          | ~ (v3_pre_topc @ X42 @ X39)
% 0.20/0.55          | ~ (r2_hidden @ X43 @ X42)
% 0.20/0.55          | ~ (r1_tarski @ X42 @ (u1_struct_0 @ X41))
% 0.20/0.55          | (r1_tmap_1 @ X39 @ X38 @ X44 @ X43)
% 0.20/0.55          | ~ (r1_tmap_1 @ X41 @ X38 @ 
% 0.20/0.55               (k3_tmap_1 @ X40 @ X38 @ X39 @ X41 @ X44) @ X43)
% 0.20/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X41))
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.20/0.55          | ~ (m1_pre_topc @ X41 @ X39)
% 0.20/0.55          | ~ (m1_pre_topc @ X39 @ X40)
% 0.20/0.55          | (v2_struct_0 @ X39)
% 0.20/0.55          | ~ (l1_pre_topc @ X38)
% 0.20/0.55          | ~ (v2_pre_topc @ X38)
% 0.20/0.55          | (v2_struct_0 @ X38))),
% 0.20/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.55          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.55  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.55          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_A)
% 0.20/0.55           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.55           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.55           | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.55           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '65'])).
% 0.20/0.55  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('69', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('70', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('71', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('72', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('73', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_A)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.55           | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.55           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['66', '67', '68', '69', '70', '71', '72', '73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.55         | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '74'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.55      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '51'])).
% 0.20/0.55  thf(t16_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.55                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.55          | ((X25) != (u1_struct_0 @ X23))
% 0.20/0.55          | ~ (v1_tsep_1 @ X23 @ X24)
% 0.20/0.55          | ~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.55          | (v3_pre_topc @ X25 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55          | ~ (l1_pre_topc @ X24)
% 0.20/0.55          | ~ (v2_pre_topc @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (v2_pre_topc @ X24)
% 0.20/0.55          | ~ (l1_pre_topc @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.55          | (v3_pre_topc @ (u1_struct_0 @ X23) @ X24)
% 0.20/0.55          | ~ (v1_tsep_1 @ X23 @ X24)
% 0.20/0.55          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.20/0.55      inference('simplify', [status(thm)], ['79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.55        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.20/0.55        | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_D)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['78', '80'])).
% 0.20/0.55  thf('82', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('83', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('84', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('85', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.55          | (v2_pre_topc @ X11)
% 0.20/0.55          | ~ (l1_pre_topc @ X12)
% 0.20/0.55          | ~ (v2_pre_topc @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.55  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('90', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.55  thf('91', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['81', '82', '83', '84', '90'])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.55         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['75', '77', '91'])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         | (v2_struct_0 @ sk_A)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '92'])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_A)
% 0.20/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_C @ sk_F @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '29'])).
% 0.20/0.55  thf(t5_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.55          | ~ (v1_xboole_0 @ X10)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_A)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | (v2_struct_0 @ sk_B)
% 0.20/0.55           | ~ (r2_hidden @ X0 @ (sk_C @ sk_F @ sk_C_1))))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['95', '98'])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['40', '99'])).
% 0.20/0.55  thf('101', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.55  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('clc', [status(thm)], ['102', '103'])).
% 0.20/0.55  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_C_1))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.55      inference('clc', [status(thm)], ['104', '105'])).
% 0.20/0.55  thf('107', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('108', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.20/0.55       ~
% 0.20/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.20/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.55      inference('split', [status(esa)], ['53'])).
% 0.20/0.55  thf('110', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('111', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('split', [status(esa)], ['53'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t81_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                       ( ![F:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                           ( ![G:$i]:
% 0.20/0.55                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.55                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.55                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.55                                 ( r1_tmap_1 @
% 0.20/0.55                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.55                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X31)
% 0.20/0.55          | ~ (v2_pre_topc @ X31)
% 0.20/0.55          | ~ (l1_pre_topc @ X31)
% 0.20/0.55          | (v2_struct_0 @ X32)
% 0.20/0.55          | ~ (m1_pre_topc @ X32 @ X33)
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 0.20/0.55          | ~ (m1_pre_topc @ X32 @ X35)
% 0.20/0.55          | ~ (r1_tmap_1 @ X35 @ X31 @ X36 @ X34)
% 0.20/0.55          | ((X34) != (X37))
% 0.20/0.55          | (r1_tmap_1 @ X32 @ X31 @ 
% 0.20/0.55             (k3_tmap_1 @ X33 @ X31 @ X35 @ X32 @ X36) @ X37)
% 0.20/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X32))
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X31))))
% 0.20/0.55          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X31))
% 0.20/0.55          | ~ (v1_funct_1 @ X36)
% 0.20/0.55          | ~ (m1_pre_topc @ X35 @ X33)
% 0.20/0.55          | (v2_struct_0 @ X35)
% 0.20/0.55          | ~ (l1_pre_topc @ X33)
% 0.20/0.55          | ~ (v2_pre_topc @ X33)
% 0.20/0.55          | (v2_struct_0 @ X33))),
% 0.20/0.55      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X33)
% 0.20/0.55          | ~ (v2_pre_topc @ X33)
% 0.20/0.55          | ~ (l1_pre_topc @ X33)
% 0.20/0.55          | (v2_struct_0 @ X35)
% 0.20/0.55          | ~ (m1_pre_topc @ X35 @ X33)
% 0.20/0.55          | ~ (v1_funct_1 @ X36)
% 0.20/0.55          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X31))
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X31))))
% 0.20/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X32))
% 0.20/0.55          | (r1_tmap_1 @ X32 @ X31 @ 
% 0.20/0.55             (k3_tmap_1 @ X33 @ X31 @ X35 @ X32 @ X36) @ X37)
% 0.20/0.55          | ~ (r1_tmap_1 @ X35 @ X31 @ X36 @ X37)
% 0.20/0.55          | ~ (m1_pre_topc @ X32 @ X35)
% 0.20/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.20/0.55          | ~ (m1_pre_topc @ X32 @ X33)
% 0.20/0.55          | (v2_struct_0 @ X32)
% 0.20/0.55          | ~ (l1_pre_topc @ X31)
% 0.20/0.55          | ~ (v2_pre_topc @ X31)
% 0.20/0.55          | (v2_struct_0 @ X31))),
% 0.20/0.55      inference('simplify', [status(thm)], ['114'])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.55          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.55             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (l1_pre_topc @ X1)
% 0.20/0.55          | ~ (v2_pre_topc @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['113', '115'])).
% 0.20/0.55  thf('117', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('119', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('121', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.55          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.55             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (l1_pre_topc @ X1)
% 0.20/0.55          | ~ (v2_pre_topc @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1))),
% 0.20/0.55      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 0.20/0.55  thf('122', plain,
% 0.20/0.55      ((![X0 : $i, X1 : $i]:
% 0.20/0.55          ((v2_struct_0 @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.55           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55           | (v2_struct_0 @ X1)
% 0.20/0.55           | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['112', '121'])).
% 0.20/0.55  thf('123', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('124', plain,
% 0.20/0.55      ((![X0 : $i, X1 : $i]:
% 0.20/0.55          ((v2_struct_0 @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.55           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55           | (v2_struct_0 @ X1)
% 0.20/0.55           | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('demod', [status(thm)], ['122', '123'])).
% 0.20/0.55  thf('125', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_B)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.55           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ X0)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['111', '124'])).
% 0.20/0.55  thf('126', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('127', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_B)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.55           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ X0)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('demod', [status(thm)], ['125', '126'])).
% 0.20/0.55  thf('128', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_A)
% 0.20/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.55         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['110', '127'])).
% 0.20/0.55  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('131', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('132', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_A)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.55            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.37/0.55  thf('133', plain,
% 0.37/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('134', plain, (((sk_F) = (sk_G))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('135', plain,
% 0.37/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.37/0.55      inference('demod', [status(thm)], ['133', '134'])).
% 0.37/0.55  thf('136', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_C_1)
% 0.37/0.55         | (v2_struct_0 @ sk_D)
% 0.37/0.55         | (v2_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.37/0.55             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['132', '135'])).
% 0.37/0.55  thf('137', plain, (~ (v2_struct_0 @ sk_D)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('138', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.37/0.55             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['136', '137'])).
% 0.37/0.55  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('140', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.37/0.55             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.37/0.55      inference('clc', [status(thm)], ['138', '139'])).
% 0.37/0.55  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('142', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_C_1))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.37/0.55             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.37/0.55      inference('clc', [status(thm)], ['140', '141'])).
% 0.37/0.55  thf('143', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('144', plain,
% 0.37/0.55      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.37/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.37/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['142', '143'])).
% 0.37/0.55  thf('145', plain, ($false),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['1', '108', '109', '144'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
