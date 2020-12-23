%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P9dU22F4nD

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 988 expanded)
%              Number of leaves         :   40 ( 290 expanded)
%              Depth                    :   29
%              Number of atoms          : 2794 (30873 expanded)
%              Number of equality atoms :   11 ( 445 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X17 )
      | ( m1_connsp_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( X28
       != ( u1_struct_0 @ X26 ) )
      | ~ ( v1_tsep_1 @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v3_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('56',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X26 ) @ X27 )
      | ~ ( v1_tsep_1 @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t7_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_connsp_2 @ ( sk_D @ X25 @ X23 @ X24 ) @ X24 @ X23 )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('80',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('81',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['78','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('104',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v3_pre_topc @ ( sk_D @ X25 @ X23 @ X24 ) @ X24 )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('115',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('116',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tarski @ ( sk_D @ X25 @ X23 @ X24 ) @ X25 )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('127',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['127'])).

thf('129',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['131'])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('134',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['127'])).

thf('135',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('136',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ( X36 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('137',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X33 )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['134','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['133','148'])).

thf('150',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['131'])).

thf('153',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['127'])).

thf('163',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['132','161','162'])).

thf('164',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['130','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_tmap_1,axiom,(
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
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('166',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( v3_pre_topc @ X40 @ X37 )
      | ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X38 ) )
      | ( X39 != X41 )
      | ~ ( r1_tmap_1 @ X38 @ X42 @ ( k2_tmap_1 @ X37 @ X42 @ X43 @ X38 ) @ X41 )
      | ( r1_tmap_1 @ X37 @ X42 @ X43 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('167',plain,(
    ! [X37: $i,X38: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X38 ) )
      | ( r1_tmap_1 @ X37 @ X42 @ X43 @ X41 )
      | ~ ( r1_tmap_1 @ X38 @ X42 @ ( k2_tmap_1 @ X37 @ X42 @ X43 @ X38 ) @ X41 )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X41 @ X40 )
      | ~ ( v3_pre_topc @ X40 @ X37 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X2 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','167'])).

thf('169',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X2 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169','170','171','172','173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['164','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('178',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','180'])).

thf('182',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['125','181'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','183'])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','185'])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['131'])).

thf('189',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['132','161'])).

thf('190',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('193',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    $false ),
    inference(demod,[status(thm)],['0','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P9dU22F4nD
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 196 iterations in 0.128s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
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
% 0.41/0.60  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_m1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.60  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.41/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.41/0.60  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('21', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf(dt_m1_connsp_2, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.41/0.60           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X12)
% 0.41/0.60          | ~ (v2_pre_topc @ X12)
% 0.41/0.60          | (v2_struct_0 @ X12)
% 0.41/0.60          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.41/0.60          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.41/0.60          | ~ (m1_connsp_2 @ X14 @ X12 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.41/0.60          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.41/0.60          | (v2_struct_0 @ sk_D_1)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_D_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((v2_pre_topc @ sk_D_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.60  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.41/0.60          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.41/0.60          | (v2_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.41/0.60  thf('27', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.41/0.60          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.41/0.60      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['20', '28'])).
% 0.41/0.60  thf(t6_connsp_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.60               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.60          | ~ (m1_connsp_2 @ X20 @ X21 @ X22)
% 0.41/0.60          | (r2_hidden @ X22 @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.41/0.60          | ~ (l1_pre_topc @ X21)
% 0.41/0.60          | ~ (v2_pre_topc @ X21)
% 0.41/0.60          | (v2_struct_0 @ X21))),
% 0.41/0.60      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D_1)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.41/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.60  thf('33', plain, ((l1_pre_topc @ sk_D_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D_1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.41/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '34'])).
% 0.41/0.60  thf('36', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1)) | (v2_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('39', plain, ((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))),
% 0.41/0.60      inference('clc', [status(thm)], ['37', '38'])).
% 0.41/0.60  thf('40', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf(t2_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ X1)
% 0.41/0.60          | (v1_xboole_0 @ X1)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.60  thf('43', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('44', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t1_tsep_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.60           ( m1_subset_1 @
% 0.41/0.60             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X29 : $i, X30 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X29 @ X30)
% 0.41/0.60          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.41/0.60          | ~ (l1_pre_topc @ X30))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.41/0.60        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf(t5_connsp_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.60               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.41/0.60                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.60          | ~ (v3_pre_topc @ X17 @ X18)
% 0.41/0.60          | ~ (r2_hidden @ X19 @ X17)
% 0.41/0.60          | (m1_connsp_2 @ X17 @ X18 @ X19)
% 0.41/0.60          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.41/0.60          | ~ (l1_pre_topc @ X18)
% 0.41/0.60          | ~ (v2_pre_topc @ X18)
% 0.41/0.60          | (v2_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf(t16_tsep_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.41/0.60                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.41/0.60                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X26 @ X27)
% 0.41/0.60          | ((X28) != (u1_struct_0 @ X26))
% 0.41/0.60          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.41/0.60          | ~ (m1_pre_topc @ X26 @ X27)
% 0.41/0.60          | (v3_pre_topc @ X28 @ X27)
% 0.41/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.60          | ~ (l1_pre_topc @ X27)
% 0.41/0.60          | ~ (v2_pre_topc @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (~ (v2_pre_topc @ X27)
% 0.41/0.60          | ~ (l1_pre_topc @ X27)
% 0.41/0.60          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.41/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.60          | (v3_pre_topc @ (u1_struct_0 @ X26) @ X27)
% 0.41/0.60          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.41/0.60          | ~ (m1_pre_topc @ X26 @ X27))),
% 0.41/0.60      inference('simplify', [status(thm)], ['55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.41/0.60        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.41/0.60        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60        | ~ (v2_pre_topc @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['54', '56'])).
% 0.41/0.60  thf('58', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('59', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('62', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.41/0.60      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['53', '62'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '63'])).
% 0.41/0.60  thf('65', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.41/0.60        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['64', '65'])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '66'])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf(t7_connsp_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.41/0.60                    ( ![D:$i]:
% 0.41/0.60                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.60                          ( m1_subset_1 @
% 0.41/0.60                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.41/0.60                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.41/0.60          | (m1_connsp_2 @ (sk_D @ X25 @ X23 @ X24) @ X24 @ X23)
% 0.41/0.60          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.41/0.60          | ~ (l1_pre_topc @ X24)
% 0.41/0.60          | ~ (v2_pre_topc @ X24)
% 0.41/0.60          | (v2_struct_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.41/0.60  thf('70', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.41/0.60             sk_B @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.60  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.41/0.60             sk_B @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.60        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60           sk_B @ sk_E)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['67', '73'])).
% 0.41/0.60  thf('75', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('76', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60           sk_B @ sk_E)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.60  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('78', plain,
% 0.41/0.60      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B @ 
% 0.41/0.60         sk_E)
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['76', '77'])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '66'])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.41/0.60          | (m1_subset_1 @ (sk_D @ X25 @ X23 @ X24) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.41/0.60          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.41/0.60          | ~ (l1_pre_topc @ X24)
% 0.41/0.60          | ~ (v2_pre_topc @ X24)
% 0.41/0.60          | (v2_struct_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.60  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('85', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.41/0.60  thf('86', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.60        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['79', '85'])).
% 0.41/0.60  thf('87', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['86', '87'])).
% 0.41/0.60  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('90', plain,
% 0.41/0.60      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['88', '89'])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.60          | ~ (m1_connsp_2 @ X20 @ X21 @ X22)
% 0.41/0.60          | (r2_hidden @ X22 @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.41/0.60          | ~ (l1_pre_topc @ X21)
% 0.41/0.60          | ~ (v2_pre_topc @ X21)
% 0.41/0.60          | (v2_struct_0 @ X21))),
% 0.41/0.60      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | (v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | (r2_hidden @ X0 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.60          | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60               sk_B @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['90', '91'])).
% 0.41/0.60  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('95', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | (v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | (r2_hidden @ X0 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.60          | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60               sk_B @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.41/0.60  thf('96', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.60        | (v2_struct_0 @ sk_B)
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['78', '95'])).
% 0.41/0.60  thf('97', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('98', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.60        | (v2_struct_0 @ sk_B)
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['96', '97'])).
% 0.41/0.60  thf('99', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['98'])).
% 0.41/0.60  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('101', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B)))),
% 0.41/0.60      inference('clc', [status(thm)], ['99', '100'])).
% 0.41/0.60  thf('102', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '66'])).
% 0.41/0.60  thf('103', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('104', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.41/0.60          | (v3_pre_topc @ (sk_D @ X25 @ X23 @ X24) @ X24)
% 0.41/0.60          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.41/0.60          | ~ (l1_pre_topc @ X24)
% 0.41/0.60          | ~ (v2_pre_topc @ X24)
% 0.41/0.60          | (v2_struct_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.41/0.60  thf('105', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['103', '104'])).
% 0.41/0.60  thf('106', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('108', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ sk_B)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.41/0.60  thf('109', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.60        | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['102', '108'])).
% 0.41/0.60  thf('110', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('111', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['109', '110'])).
% 0.41/0.60  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('113', plain,
% 0.41/0.60      (((v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B)
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['111', '112'])).
% 0.41/0.60  thf('114', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '66'])).
% 0.41/0.60  thf('115', plain,
% 0.41/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('116', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.41/0.60          | (r1_tarski @ (sk_D @ X25 @ X23 @ X24) @ X25)
% 0.41/0.60          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.41/0.60          | ~ (l1_pre_topc @ X24)
% 0.41/0.60          | ~ (v2_pre_topc @ X24)
% 0.41/0.60          | (v2_struct_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.41/0.60  thf('117', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.41/0.60             (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['115', '116'])).
% 0.41/0.60  thf('118', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('120', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.41/0.60          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.41/0.60             (u1_struct_0 @ sk_D_1))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.41/0.60  thf('121', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.60        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60           (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['114', '120'])).
% 0.41/0.60  thf('122', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('123', plain,
% 0.41/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60           (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['121', '122'])).
% 0.41/0.60  thf('124', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('125', plain,
% 0.41/0.60      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60         (u1_struct_0 @ sk_D_1))
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['123', '124'])).
% 0.41/0.60  thf('126', plain,
% 0.41/0.60      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['88', '89'])).
% 0.41/0.60  thf('127', plain,
% 0.41/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.41/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('128', plain,
% 0.41/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.41/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.41/0.60      inference('split', [status(esa)], ['127'])).
% 0.41/0.60  thf('129', plain, (((sk_E) = (sk_F))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('130', plain,
% 0.41/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.41/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.41/0.60      inference('demod', [status(thm)], ['128', '129'])).
% 0.41/0.60  thf('131', plain,
% 0.41/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.41/0.60        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('132', plain,
% 0.41/0.60      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.41/0.60       ~
% 0.41/0.60       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.41/0.60      inference('split', [status(esa)], ['131'])).
% 0.41/0.60  thf('133', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('134', plain,
% 0.41/0.60      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.41/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.60      inference('split', [status(esa)], ['127'])).
% 0.41/0.60  thf('135', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t64_tmap_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
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
% 0.41/0.61  thf('136', plain,
% 0.41/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X31)
% 0.41/0.61          | ~ (v2_pre_topc @ X31)
% 0.41/0.61          | ~ (l1_pre_topc @ X31)
% 0.41/0.61          | (v2_struct_0 @ X32)
% 0.41/0.61          | ~ (m1_pre_topc @ X32 @ X31)
% 0.41/0.61          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.41/0.61          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.41/0.61          | ((X36) != (X33))
% 0.41/0.61          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 0.41/0.61          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.41/0.61          | ~ (m1_subset_1 @ X35 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.41/0.61          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.41/0.61          | ~ (v1_funct_1 @ X35)
% 0.41/0.61          | ~ (l1_pre_topc @ X34)
% 0.41/0.61          | ~ (v2_pre_topc @ X34)
% 0.41/0.61          | (v2_struct_0 @ X34))),
% 0.41/0.61      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.41/0.61  thf('137', plain,
% 0.41/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X34)
% 0.41/0.61          | ~ (v2_pre_topc @ X34)
% 0.41/0.61          | ~ (l1_pre_topc @ X34)
% 0.41/0.61          | ~ (v1_funct_1 @ X35)
% 0.41/0.61          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.41/0.61          | ~ (m1_subset_1 @ X35 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.41/0.61          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.41/0.61          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 0.41/0.61          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.41/0.61          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.41/0.61          | ~ (m1_pre_topc @ X32 @ X31)
% 0.41/0.61          | (v2_struct_0 @ X32)
% 0.41/0.61          | ~ (l1_pre_topc @ X31)
% 0.41/0.61          | ~ (v2_pre_topc @ X31)
% 0.41/0.61          | (v2_struct_0 @ X31))),
% 0.41/0.61      inference('simplify', [status(thm)], ['136'])).
% 0.41/0.61  thf('138', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.41/0.61             X1)
% 0.41/0.61          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v1_funct_1 @ sk_C_1)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['135', '137'])).
% 0.41/0.61  thf('139', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('140', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('141', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('142', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('145', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.41/0.61             X1)
% 0.41/0.61          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['138', '139', '140', '141', '142', '143', '144'])).
% 0.41/0.61  thf('146', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((v2_struct_0 @ sk_A)
% 0.41/0.61           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.61           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.41/0.61           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.41/0.61           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61           | (v2_struct_0 @ X0)
% 0.41/0.61           | (v2_struct_0 @ sk_B)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['134', '145'])).
% 0.41/0.61  thf('147', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('148', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((v2_struct_0 @ sk_A)
% 0.41/0.61           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.41/0.61           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.41/0.61           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61           | (v2_struct_0 @ X0)
% 0.41/0.61           | (v2_struct_0 @ sk_B)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('demod', [status(thm)], ['146', '147'])).
% 0.41/0.61  thf('149', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_B)
% 0.41/0.61         | (v2_struct_0 @ sk_D_1)
% 0.41/0.61         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.41/0.61         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.41/0.61         | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['133', '148'])).
% 0.41/0.61  thf('150', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('151', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_B)
% 0.41/0.61         | (v2_struct_0 @ sk_D_1)
% 0.41/0.61         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.41/0.61         | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('demod', [status(thm)], ['149', '150'])).
% 0.41/0.61  thf('152', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['131'])).
% 0.41/0.61  thf('153', plain, (((sk_E) = (sk_F))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('154', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['152', '153'])).
% 0.41/0.61  thf('155', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.41/0.61             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['151', '154'])).
% 0.41/0.61  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('157', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.41/0.61             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('clc', [status(thm)], ['155', '156'])).
% 0.41/0.61  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('159', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_D_1))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.41/0.61             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('clc', [status(thm)], ['157', '158'])).
% 0.41/0.61  thf('160', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('161', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.41/0.61       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.41/0.61      inference('sup-', [status(thm)], ['159', '160'])).
% 0.41/0.61  thf('162', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.41/0.61       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.41/0.61      inference('split', [status(esa)], ['127'])).
% 0.41/0.61  thf('163', plain,
% 0.41/0.61      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['132', '161', '162'])).
% 0.41/0.61  thf('164', plain,
% 0.41/0.61      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.41/0.61        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['130', '163'])).
% 0.41/0.61  thf('165', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_1 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t66_tmap_1, axiom,
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
% 0.41/0.61                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.41/0.61                                   ( r2_hidden @ F @ E ) & 
% 0.41/0.61                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.41/0.61                                   ( ( F ) = ( G ) ) ) =>
% 0.41/0.61                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.41/0.61                                   ( r1_tmap_1 @
% 0.41/0.61                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('166', plain,
% 0.41/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X37)
% 0.41/0.61          | ~ (v2_pre_topc @ X37)
% 0.41/0.61          | ~ (l1_pre_topc @ X37)
% 0.41/0.61          | (v2_struct_0 @ X38)
% 0.41/0.61          | ~ (m1_pre_topc @ X38 @ X37)
% 0.41/0.61          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.41/0.61          | ~ (v3_pre_topc @ X40 @ X37)
% 0.41/0.61          | ~ (r2_hidden @ X39 @ X40)
% 0.41/0.61          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.41/0.61          | ((X39) != (X41))
% 0.41/0.61          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.41/0.61               X41)
% 0.41/0.61          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X39)
% 0.41/0.61          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.41/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.41/0.61          | ~ (m1_subset_1 @ X43 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.41/0.61          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.41/0.61          | ~ (v1_funct_1 @ X43)
% 0.41/0.61          | ~ (l1_pre_topc @ X42)
% 0.41/0.61          | ~ (v2_pre_topc @ X42)
% 0.41/0.61          | (v2_struct_0 @ X42))),
% 0.41/0.61      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.41/0.61  thf('167', plain,
% 0.41/0.61      (![X37 : $i, X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X42)
% 0.41/0.61          | ~ (v2_pre_topc @ X42)
% 0.41/0.61          | ~ (l1_pre_topc @ X42)
% 0.41/0.61          | ~ (v1_funct_1 @ X43)
% 0.41/0.61          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.41/0.61          | ~ (m1_subset_1 @ X43 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.41/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.41/0.61          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.41/0.61          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X41)
% 0.41/0.61          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.41/0.61               X41)
% 0.41/0.61          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.41/0.61          | ~ (r2_hidden @ X41 @ X40)
% 0.41/0.61          | ~ (v3_pre_topc @ X40 @ X37)
% 0.41/0.61          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 0.41/0.61          | ~ (m1_pre_topc @ X38 @ X37)
% 0.41/0.61          | (v2_struct_0 @ X38)
% 0.41/0.61          | ~ (l1_pre_topc @ X37)
% 0.41/0.61          | ~ (v2_pre_topc @ X37)
% 0.41/0.61          | (v2_struct_0 @ X37))),
% 0.41/0.61      inference('simplify', [status(thm)], ['166'])).
% 0.41/0.61  thf('168', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.41/0.61          | ~ (r2_hidden @ X1 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v1_funct_1 @ sk_C_1)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['165', '167'])).
% 0.41/0.61  thf('169', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('170', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('171', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('172', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('175', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.41/0.61          | ~ (r2_hidden @ X1 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.61               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.41/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['168', '169', '170', '171', '172', '173', '174'])).
% 0.41/0.61  thf('176', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (r2_hidden @ sk_E @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['164', '175'])).
% 0.41/0.61  thf('177', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('178', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('179', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('180', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (r2_hidden @ sk_E @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 0.41/0.61  thf('181', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B)
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.61        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.41/0.61             (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['126', '180'])).
% 0.41/0.61  thf('182', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.61        | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['125', '181'])).
% 0.41/0.61  thf('183', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | ~ (v3_pre_topc @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B)
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['182'])).
% 0.41/0.61  thf('184', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['113', '183'])).
% 0.41/0.61  thf('185', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | ~ (r2_hidden @ sk_E @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B))
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['184'])).
% 0.41/0.61  thf('186', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['101', '185'])).
% 0.41/0.61  thf('187', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['186'])).
% 0.41/0.61  thf('188', plain,
% 0.41/0.61      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.41/0.61         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.41/0.61      inference('split', [status(esa)], ['131'])).
% 0.41/0.61  thf('189', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['132', '161'])).
% 0.41/0.61  thf('190', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['188', '189'])).
% 0.41/0.61  thf('191', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_D_1)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['187', '190'])).
% 0.41/0.61  thf('192', plain,
% 0.41/0.61      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['20', '28'])).
% 0.41/0.61  thf(t5_subset, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.41/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.41/0.61  thf('193', plain,
% 0.41/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.61          | ~ (v1_xboole_0 @ X4)
% 0.41/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.61  thf('194', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['192', '193'])).
% 0.41/0.61  thf('195', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D_1)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['191', '194'])).
% 0.41/0.61  thf('196', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '195'])).
% 0.41/0.61  thf('197', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('198', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.41/0.61      inference('clc', [status(thm)], ['196', '197'])).
% 0.41/0.61  thf('199', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('200', plain, ((v2_struct_0 @ sk_D_1)),
% 0.41/0.61      inference('clc', [status(thm)], ['198', '199'])).
% 0.41/0.61  thf('201', plain, ($false), inference('demod', [status(thm)], ['0', '200'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
