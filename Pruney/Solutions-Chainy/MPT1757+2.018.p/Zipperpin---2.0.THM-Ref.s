%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HsAb8qoHBB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 703 expanded)
%              Number of leaves         :   39 ( 212 expanded)
%              Depth                    :   27
%              Number of atoms          : 2257 (21992 expanded)
%              Number of equality atoms :   11 ( 323 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t67_tmap_1,conjecture,(
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
                              <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_connsp_2 @ ( sk_C @ X16 @ X15 ) @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['17','18'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_connsp_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('25',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_connsp_2 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('33',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_E @ ( sk_C @ sk_E @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('37',plain,
    ( ( r2_hidden @ sk_E @ ( sk_C @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_E @ ( sk_C @ sk_E @ sk_D_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t9_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( m1_connsp_2 @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 @ X22 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

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

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( X26
       != ( u1_struct_0 @ X24 ) )
      | ~ ( v1_tsep_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X24 ) @ X25 )
      | ~ ( v1_tsep_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52','61'])).

thf('63',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['67','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','65'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_connsp_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('98',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(split,[status(esa)],['91'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('100',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ( X34 != X31 )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('101',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X31 )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sup-',[status(thm)],['98','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sup-',[status(thm)],['97','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['95'])).

thf('117',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(split,[status(esa)],['91'])).

thf('127',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['96','125','126'])).

thf('128',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['94','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
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
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('130',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X37 )
      | ( X37 != X39 )
      | ~ ( r1_tmap_1 @ X36 @ X40 @ ( k2_tmap_1 @ X35 @ X40 @ X41 @ X36 ) @ X39 )
      | ( r1_tmap_1 @ X35 @ X40 @ X41 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('131',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ( r1_tmap_1 @ X35 @ X40 @ X41 @ X39 )
      | ~ ( r1_tmap_1 @ X36 @ X40 @ ( k2_tmap_1 @ X35 @ X40 @ X41 @ X36 ) @ X39 )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X39 )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('142',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','144'])).

thf('146',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['80','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','147'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(split,[status(esa)],['95'])).

thf('151',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['96','125'])).

thf('152',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('155',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['0','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HsAb8qoHBB
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 193 iterations in 0.146s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.41/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(t67_tmap_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.60                 ( m1_subset_1 @
% 0.41/0.60                   C @ 
% 0.41/0.60                   ( k1_zfmisc_1 @
% 0.41/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.41/0.60                     ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.60                       ( ![F:$i]:
% 0.41/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.60                           ( ( ( E ) = ( F ) ) =>
% 0.41/0.60                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.41/0.60                               ( r1_tmap_1 @
% 0.41/0.60                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60            ( l1_pre_topc @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60                ( l1_pre_topc @ B ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                    ( v1_funct_2 @
% 0.41/0.60                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.60                    ( m1_subset_1 @
% 0.41/0.60                      C @ 
% 0.41/0.60                      ( k1_zfmisc_1 @
% 0.41/0.60                        ( k2_zfmisc_1 @
% 0.41/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.60                  ( ![D:$i]:
% 0.41/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.41/0.60                        ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.60                      ( ![E:$i]:
% 0.41/0.60                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.60                          ( ![F:$i]:
% 0.41/0.60                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.60                              ( ( ( E ) = ( F ) ) =>
% 0.41/0.60                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.41/0.60                                  ( r1_tmap_1 @
% 0.41/0.60                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.41/0.60  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('2', plain, (((sk_E) = (sk_F))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf(existence_m1_connsp_2, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X15)
% 0.41/0.60          | ~ (v2_pre_topc @ X15)
% 0.41/0.60          | (v2_struct_0 @ X15)
% 0.41/0.60          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.41/0.60          | (m1_connsp_2 @ (sk_C @ X16 @ X15) @ X15 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.41/0.60        | (v2_struct_0 @ sk_D_1)
% 0.41/0.60        | ~ (v2_pre_topc @ sk_D_1)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_D_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('6', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X5 @ X6)
% 0.41/0.60          | (v2_pre_topc @ X5)
% 0.41/0.60          | ~ (l1_pre_topc @ X6)
% 0.41/0.60          | ~ (v2_pre_topc @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_B)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60        | (v2_pre_topc @ sk_D_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('11', plain, ((v2_pre_topc @ sk_D_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.61  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_m1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.61  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.61  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.41/0.61  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('19', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.41/0.61      inference('clc', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.41/0.61      inference('clc', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf('21', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf(dt_m1_connsp_2, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.61         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61       ( ![C:$i]:
% 0.41/0.61         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.41/0.61           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X12)
% 0.41/0.61          | ~ (v2_pre_topc @ X12)
% 0.41/0.61          | (v2_struct_0 @ X12)
% 0.41/0.61          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.41/0.61          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.41/0.61          | ~ (m1_connsp_2 @ X14 @ X12 @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.41/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_D_1)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_D_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.61  thf('24', plain, ((v2_pre_topc @ sk_D_1)),
% 0.41/0.61      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.61  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.41/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.41/0.61          | (v2_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.41/0.61  thf('27', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.41/0.61          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.41/0.61      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['20', '28'])).
% 0.41/0.61  thf(t6_connsp_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.61          | ~ (m1_connsp_2 @ X17 @ X18 @ X19)
% 0.41/0.61          | (r2_hidden @ X19 @ X17)
% 0.41/0.61          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.41/0.61          | ~ (l1_pre_topc @ X18)
% 0.41/0.61          | ~ (v2_pre_topc @ X18)
% 0.41/0.61          | (v2_struct_0 @ X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_D_1)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_D_1)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_D_1)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.41/0.61          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.41/0.61      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.61  thf('33', plain, ((l1_pre_topc @ sk_D_1)),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_D_1)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.41/0.61          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))
% 0.41/0.61        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '34'])).
% 0.41/0.61  thf('36', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1)) | (v2_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.61  thf('38', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('39', plain, ((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))),
% 0.41/0.61      inference('clc', [status(thm)], ['37', '38'])).
% 0.41/0.61  thf('40', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf(t2_subset, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r2_hidden @ X0 @ X1)
% 0.41/0.61          | (v1_xboole_0 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('43', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t1_tsep_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.61           ( m1_subset_1 @
% 0.41/0.61             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X27 : $i, X28 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X27 @ X28)
% 0.41/0.61          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.41/0.61          | ~ (l1_pre_topc @ X28))),
% 0.41/0.61      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_B)
% 0.41/0.61        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.61  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf(t9_connsp_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( v3_pre_topc @ B @ A ) <=>
% 0.41/0.61             ( ![C:$i]:
% 0.41/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.41/0.61                      ( ![D:$i]:
% 0.41/0.61                        ( ( m1_subset_1 @
% 0.41/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.41/0.61                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.61          | ~ (v3_pre_topc @ X20 @ X21)
% 0.41/0.61          | (m1_connsp_2 @ (sk_D @ X22 @ X20 @ X21) @ X21 @ X22)
% 0.41/0.61          | ~ (r2_hidden @ X22 @ X20)
% 0.41/0.61          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.41/0.61          | ~ (l1_pre_topc @ X21)
% 0.41/0.61          | ~ (v2_pre_topc @ X21)
% 0.41/0.61          | (v2_struct_0 @ X21))),
% 0.41/0.61      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             sk_B @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.61  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf(t16_tsep_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.41/0.61                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.41/0.61                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X24 @ X25)
% 0.41/0.61          | ((X26) != (u1_struct_0 @ X24))
% 0.41/0.61          | ~ (v1_tsep_1 @ X24 @ X25)
% 0.41/0.61          | ~ (m1_pre_topc @ X24 @ X25)
% 0.41/0.61          | (v3_pre_topc @ X26 @ X25)
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | ~ (l1_pre_topc @ X25)
% 0.41/0.61          | ~ (v2_pre_topc @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X25)
% 0.41/0.61          | ~ (l1_pre_topc @ X25)
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | (v3_pre_topc @ (u1_struct_0 @ X24) @ X25)
% 0.41/0.61          | ~ (v1_tsep_1 @ X24 @ X25)
% 0.41/0.61          | ~ (m1_pre_topc @ X24 @ X25))),
% 0.41/0.61      inference('simplify', [status(thm)], ['54'])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.41/0.61        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.41/0.61        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['53', '55'])).
% 0.41/0.61  thf('57', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('58', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('60', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('61', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             sk_B @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['50', '51', '52', '61'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.41/0.61         sk_E)
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['43', '62'])).
% 0.41/0.61  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61           sk_B @ sk_E))),
% 0.41/0.61      inference('clc', [status(thm)], ['63', '64'])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61           sk_B @ sk_E))),
% 0.41/0.61      inference('sup-', [status(thm)], ['42', '65'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('68', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.61          | ~ (v3_pre_topc @ X20 @ X21)
% 0.41/0.61          | (r1_tarski @ (sk_D @ X22 @ X20 @ X21) @ X20)
% 0.41/0.61          | ~ (r2_hidden @ X22 @ X20)
% 0.41/0.61          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.41/0.61          | ~ (l1_pre_topc @ X21)
% 0.41/0.61          | ~ (v2_pre_topc @ X21)
% 0.41/0.61          | (v2_struct_0 @ X21))),
% 0.41/0.61      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.61  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.41/0.61  thf('75', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61         (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['68', '76'])).
% 0.41/0.61  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61           (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['77', '78'])).
% 0.41/0.61  thf('80', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61           (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['67', '79'])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61           sk_B @ sk_E))),
% 0.41/0.61      inference('sup-', [status(thm)], ['42', '65'])).
% 0.41/0.61  thf('82', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('83', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X12)
% 0.41/0.61          | ~ (v2_pre_topc @ X12)
% 0.41/0.61          | (v2_struct_0 @ X12)
% 0.41/0.61          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.41/0.61          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.41/0.61          | ~ (m1_connsp_2 @ X14 @ X12 @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.41/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.41/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.41/0.61  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('89', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E))),
% 0.41/0.61      inference('clc', [status(thm)], ['87', '88'])).
% 0.41/0.61  thf('90', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['81', '89'])).
% 0.41/0.61  thf('91', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['91'])).
% 0.41/0.61  thf('93', plain, (((sk_E) = (sk_F))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('94', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['92', '93'])).
% 0.41/0.61  thf('95', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)
% 0.41/0.61        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('96', plain,
% 0.41/0.61      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)) | 
% 0.41/0.61       ~
% 0.41/0.61       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))),
% 0.41/0.61      inference('split', [status(esa)], ['95'])).
% 0.41/0.61  thf('97', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('98', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('split', [status(esa)], ['91'])).
% 0.41/0.61  thf('99', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t64_tmap_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61             ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.61                 ( m1_subset_1 @
% 0.41/0.61                   C @ 
% 0.41/0.61                   ( k1_zfmisc_1 @
% 0.41/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.61                   ( ![E:$i]:
% 0.41/0.61                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.61                       ( ![F:$i]:
% 0.41/0.61                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.61                           ( ( ( ( E ) = ( F ) ) & 
% 0.41/0.61                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.41/0.61                             ( r1_tmap_1 @
% 0.41/0.61                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('100', plain,
% 0.41/0.61      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X29)
% 0.41/0.61          | ~ (v2_pre_topc @ X29)
% 0.41/0.61          | ~ (l1_pre_topc @ X29)
% 0.41/0.61          | (v2_struct_0 @ X30)
% 0.41/0.61          | ~ (m1_pre_topc @ X30 @ X29)
% 0.41/0.61          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.41/0.61          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.41/0.61          | ((X34) != (X31))
% 0.41/0.61          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X34)
% 0.41/0.61          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 0.41/0.61          | ~ (m1_subset_1 @ X33 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.41/0.61          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.41/0.61          | ~ (v1_funct_1 @ X33)
% 0.41/0.61          | ~ (l1_pre_topc @ X32)
% 0.41/0.61          | ~ (v2_pre_topc @ X32)
% 0.41/0.61          | (v2_struct_0 @ X32))),
% 0.41/0.61      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.41/0.61  thf('101', plain,
% 0.41/0.61      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X32)
% 0.41/0.61          | ~ (v2_pre_topc @ X32)
% 0.41/0.61          | ~ (l1_pre_topc @ X32)
% 0.41/0.61          | ~ (v1_funct_1 @ X33)
% 0.41/0.61          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.41/0.61          | ~ (m1_subset_1 @ X33 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.41/0.61          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.41/0.61          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X31)
% 0.41/0.61          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.41/0.61          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.41/0.61          | ~ (m1_pre_topc @ X30 @ X29)
% 0.41/0.61          | (v2_struct_0 @ X30)
% 0.41/0.61          | ~ (l1_pre_topc @ X29)
% 0.41/0.61          | ~ (v2_pre_topc @ X29)
% 0.41/0.61          | (v2_struct_0 @ X29))),
% 0.41/0.61      inference('simplify', [status(thm)], ['100'])).
% 0.41/0.61  thf('102', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.41/0.61             X1)
% 0.41/0.61          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v1_funct_1 @ sk_C_2)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['99', '101'])).
% 0.41/0.61  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('105', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('106', plain, ((v1_funct_1 @ sk_C_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('109', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.41/0.61             X1)
% 0.41/0.61          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['102', '103', '104', '105', '106', '107', '108'])).
% 0.41/0.61  thf('110', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((v2_struct_0 @ sk_A)
% 0.41/0.61           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.61           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ sk_E)
% 0.41/0.61           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.41/0.61           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61           | (v2_struct_0 @ X0)
% 0.41/0.61           | (v2_struct_0 @ sk_B)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['98', '109'])).
% 0.41/0.61  thf('111', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('112', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((v2_struct_0 @ sk_A)
% 0.41/0.61           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ sk_E)
% 0.41/0.61           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.41/0.61           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61           | (v2_struct_0 @ X0)
% 0.41/0.61           | (v2_struct_0 @ sk_B)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('demod', [status(thm)], ['110', '111'])).
% 0.41/0.61  thf('113', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_B)
% 0.41/0.61         | (v2_struct_0 @ sk_D_1)
% 0.41/0.61         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.41/0.61         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E)
% 0.41/0.61         | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['97', '112'])).
% 0.41/0.61  thf('114', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('115', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_B)
% 0.41/0.61         | (v2_struct_0 @ sk_D_1)
% 0.41/0.61         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E)
% 0.41/0.61         | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('demod', [status(thm)], ['113', '114'])).
% 0.41/0.61  thf('116', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['95'])).
% 0.41/0.61  thf('117', plain, (((sk_E) = (sk_F))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('118', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['116', '117'])).
% 0.41/0.61  thf('119', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) & 
% 0.41/0.61             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['115', '118'])).
% 0.41/0.61  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('121', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) & 
% 0.41/0.61             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('clc', [status(thm)], ['119', '120'])).
% 0.41/0.61  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('123', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_D_1))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) & 
% 0.41/0.61             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('clc', [status(thm)], ['121', '122'])).
% 0.41/0.61  thf('124', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('125', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) | 
% 0.41/0.61       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.41/0.61      inference('sup-', [status(thm)], ['123', '124'])).
% 0.41/0.61  thf('126', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) | 
% 0.41/0.61       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.41/0.61      inference('split', [status(esa)], ['91'])).
% 0.41/0.61  thf('127', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['96', '125', '126'])).
% 0.41/0.61  thf('128', plain,
% 0.41/0.61      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['94', '127'])).
% 0.41/0.61  thf('129', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t65_tmap_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61             ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.61                 ( m1_subset_1 @
% 0.41/0.61                   C @ 
% 0.41/0.61                   ( k1_zfmisc_1 @
% 0.41/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.61                   ( ![E:$i]:
% 0.41/0.61                     ( ( m1_subset_1 @
% 0.41/0.61                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                       ( ![F:$i]:
% 0.41/0.61                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.61                           ( ![G:$i]:
% 0.41/0.61                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.61                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.41/0.61                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.41/0.61                                   ( ( F ) = ( G ) ) ) =>
% 0.41/0.61                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.41/0.61                                   ( r1_tmap_1 @
% 0.41/0.61                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('130', plain,
% 0.41/0.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X35)
% 0.41/0.61          | ~ (v2_pre_topc @ X35)
% 0.41/0.61          | ~ (l1_pre_topc @ X35)
% 0.41/0.61          | (v2_struct_0 @ X36)
% 0.41/0.61          | ~ (m1_pre_topc @ X36 @ X35)
% 0.41/0.61          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.41/0.61          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X36))
% 0.41/0.61          | ~ (m1_connsp_2 @ X38 @ X35 @ X37)
% 0.41/0.61          | ((X37) != (X39))
% 0.41/0.61          | ~ (r1_tmap_1 @ X36 @ X40 @ (k2_tmap_1 @ X35 @ X40 @ X41 @ X36) @ 
% 0.41/0.61               X39)
% 0.41/0.61          | (r1_tmap_1 @ X35 @ X40 @ X41 @ X37)
% 0.41/0.61          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.41/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.41/0.61          | ~ (m1_subset_1 @ X41 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))))
% 0.41/0.61          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))
% 0.41/0.61          | ~ (v1_funct_1 @ X41)
% 0.41/0.61          | ~ (l1_pre_topc @ X40)
% 0.41/0.61          | ~ (v2_pre_topc @ X40)
% 0.41/0.61          | (v2_struct_0 @ X40))),
% 0.41/0.61      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.41/0.61  thf('131', plain,
% 0.41/0.61      (![X35 : $i, X36 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X40)
% 0.41/0.61          | ~ (v2_pre_topc @ X40)
% 0.41/0.61          | ~ (l1_pre_topc @ X40)
% 0.41/0.61          | ~ (v1_funct_1 @ X41)
% 0.41/0.61          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))
% 0.41/0.61          | ~ (m1_subset_1 @ X41 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))))
% 0.41/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.41/0.61          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.41/0.61          | (r1_tmap_1 @ X35 @ X40 @ X41 @ X39)
% 0.41/0.61          | ~ (r1_tmap_1 @ X36 @ X40 @ (k2_tmap_1 @ X35 @ X40 @ X41 @ X36) @ 
% 0.41/0.61               X39)
% 0.41/0.61          | ~ (m1_connsp_2 @ X38 @ X35 @ X39)
% 0.41/0.61          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X36))
% 0.41/0.61          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X35))
% 0.41/0.61          | ~ (m1_pre_topc @ X36 @ X35)
% 0.41/0.61          | (v2_struct_0 @ X36)
% 0.41/0.61          | ~ (l1_pre_topc @ X35)
% 0.41/0.61          | ~ (v2_pre_topc @ X35)
% 0.41/0.61          | (v2_struct_0 @ X35))),
% 0.41/0.61      inference('simplify', [status(thm)], ['130'])).
% 0.41/0.61  thf('132', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.41/0.61          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ X1)
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v1_funct_1 @ sk_C_2)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['129', '131'])).
% 0.41/0.61  thf('133', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('134', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('135', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('136', plain, ((v1_funct_1 @ sk_C_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('138', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('139', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.41/0.61          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ X1)
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['132', '133', '134', '135', '136', '137', '138'])).
% 0.41/0.61  thf('140', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.41/0.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['128', '139'])).
% 0.41/0.61  thf('141', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('142', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('143', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('144', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.41/0.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.41/0.61  thf('145', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | ~ (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             sk_B @ sk_E)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['90', '144'])).
% 0.41/0.61  thf('146', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             sk_B @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['80', '145'])).
% 0.41/0.61  thf('147', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.41/0.61             sk_B @ sk_E)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['146'])).
% 0.41/0.61  thf('148', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['66', '147'])).
% 0.41/0.61  thf('149', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['148'])).
% 0.41/0.61  thf('150', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))
% 0.41/0.61         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.41/0.61      inference('split', [status(esa)], ['95'])).
% 0.41/0.61  thf('151', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['96', '125'])).
% 0.41/0.61  thf('152', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['150', '151'])).
% 0.41/0.61  thf('153', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['149', '152'])).
% 0.41/0.61  thf('154', plain,
% 0.41/0.61      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['20', '28'])).
% 0.41/0.61  thf(t5_subset, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.41/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.41/0.61  thf('155', plain,
% 0.41/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.61          | ~ (v1_xboole_0 @ X4)
% 0.41/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.61  thf('156', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['154', '155'])).
% 0.41/0.61  thf('157', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['153', '156'])).
% 0.41/0.61  thf('158', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '157'])).
% 0.41/0.61  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('160', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('clc', [status(thm)], ['158', '159'])).
% 0.41/0.61  thf('161', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('162', plain, ((v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('clc', [status(thm)], ['160', '161'])).
% 0.41/0.61  thf('163', plain, ($false), inference('demod', [status(thm)], ['0', '162'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
