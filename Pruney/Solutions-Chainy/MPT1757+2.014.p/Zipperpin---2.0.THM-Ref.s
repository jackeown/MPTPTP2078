%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PeOM7IB3JW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:55 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 774 expanded)
%              Number of leaves         :   40 ( 231 expanded)
%              Depth                    :   27
%              Number of atoms          : 2438 (24156 expanded)
%              Number of equality atoms :   11 ( 351 expanded)
%              Maximal formula depth    :   28 (   7 average)

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
      | ( r1_tarski @ ( sk_D @ X25 @ X23 @ X24 ) @ X25 )
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
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
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
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('92',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('93',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('110',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['103'])).

thf('111',plain,(
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

thf('112',plain,(
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

thf('113',plain,(
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
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['110','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['109','124'])).

thf('126',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['107'])).

thf('129',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['103'])).

thf('139',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['108','137','138'])).

thf('140',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['106','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('142',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_connsp_2 @ X40 @ X37 @ X39 )
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
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('143',plain,(
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
      | ~ ( m1_connsp_2 @ X40 @ X37 @ X41 )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('154',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','156'])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['90','157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','159'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['107'])).

thf('163',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['108','137'])).

thf('164',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('167',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['0','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PeOM7IB3JW
% 0.14/0.37  % Computer   : n025.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:03:21 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.23/0.37  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 195 iterations in 0.131s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.62  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.37/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.37/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.62  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.37/0.62  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.37/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.62  thf(t67_tmap_1, conjecture,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.62             ( l1_pre_topc @ B ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.62                 ( m1_subset_1 @
% 0.37/0.62                   C @ 
% 0.37/0.62                   ( k1_zfmisc_1 @
% 0.37/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.62               ( ![D:$i]:
% 0.37/0.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.37/0.62                     ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.62                   ( ![E:$i]:
% 0.37/0.62                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.62                       ( ![F:$i]:
% 0.37/0.62                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.62                           ( ( ( E ) = ( F ) ) =>
% 0.37/0.62                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.37/0.62                               ( r1_tmap_1 @
% 0.37/0.62                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i]:
% 0.37/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.62            ( l1_pre_topc @ A ) ) =>
% 0.37/0.62          ( ![B:$i]:
% 0.37/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.62                ( l1_pre_topc @ B ) ) =>
% 0.37/0.62              ( ![C:$i]:
% 0.37/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.62                    ( v1_funct_2 @
% 0.37/0.62                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.62                    ( m1_subset_1 @
% 0.37/0.62                      C @ 
% 0.37/0.62                      ( k1_zfmisc_1 @
% 0.37/0.62                        ( k2_zfmisc_1 @
% 0.37/0.62                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.62                  ( ![D:$i]:
% 0.37/0.62                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.37/0.62                        ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.62                      ( ![E:$i]:
% 0.37/0.62                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.62                          ( ![F:$i]:
% 0.37/0.62                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.62                              ( ( ( E ) = ( F ) ) =>
% 0.37/0.62                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.37/0.62                                  ( r1_tmap_1 @
% 0.37/0.62                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.37/0.62  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('2', plain, (((sk_E) = (sk_F))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf(existence_m1_connsp_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.62         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X15)
% 0.37/0.62          | ~ (v2_pre_topc @ X15)
% 0.37/0.62          | (v2_struct_0 @ X15)
% 0.37/0.62          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.37/0.62          | (m1_connsp_2 @ (sk_C @ X16 @ X15) @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | ~ (v2_pre_topc @ sk_D_1)
% 0.37/0.62        | ~ (l1_pre_topc @ sk_D_1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('6', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc1_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X5 : $i, X6 : $i]:
% 0.37/0.62         (~ (m1_pre_topc @ X5 @ X6)
% 0.37/0.62          | (v2_pre_topc @ X5)
% 0.37/0.62          | ~ (l1_pre_topc @ X6)
% 0.37/0.62          | ~ (v2_pre_topc @ X6))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      ((~ (v2_pre_topc @ sk_B)
% 0.37/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (v2_pre_topc @ sk_D_1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('11', plain, ((v2_pre_topc @ sk_D_1)),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.62  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_m1_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]:
% 0.37/0.62         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.62  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.62  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.37/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.37/0.62  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('19', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.37/0.62      inference('clc', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.37/0.62      inference('clc', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('21', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf(dt_m1_connsp_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.62         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62       ( ![C:$i]:
% 0.37/0.62         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.37/0.62           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X12)
% 0.37/0.62          | ~ (v2_pre_topc @ X12)
% 0.37/0.62          | (v2_struct_0 @ X12)
% 0.37/0.62          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.37/0.62          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X14 @ X12 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.37/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.37/0.62          | (v2_struct_0 @ sk_D_1)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_D_1)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_D_1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf('24', plain, ((v2_pre_topc @ sk_D_1)),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.62  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.37/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.37/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.37/0.62          | (v2_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.37/0.62  thf('27', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.37/0.62      inference('clc', [status(thm)], ['26', '27'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['20', '28'])).
% 0.37/0.62  thf(t6_connsp_2, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X20 @ X21 @ X22)
% 0.37/0.62          | (r2_hidden @ X22 @ X20)
% 0.37/0.62          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.37/0.62          | ~ (l1_pre_topc @ X21)
% 0.37/0.62          | ~ (v2_pre_topc @ X21)
% 0.37/0.62          | (v2_struct_0 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_D_1)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_D_1)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_D_1)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.37/0.62          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.62  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.62  thf('33', plain, ((l1_pre_topc @ sk_D_1)),
% 0.37/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_D_1)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.37/0.62          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))
% 0.37/0.62        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['19', '34'])).
% 0.37/0.62  thf('36', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf('37', plain,
% 0.37/0.62      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1)) | (v2_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('38', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('39', plain, ((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))),
% 0.37/0.62      inference('clc', [status(thm)], ['37', '38'])).
% 0.37/0.62  thf('40', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf(t2_subset, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r2_hidden @ X0 @ X1)
% 0.37/0.62          | (v1_xboole_0 @ X1)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.62  thf('43', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('44', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t1_tsep_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.62           ( m1_subset_1 @
% 0.37/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('45', plain,
% 0.37/0.62      (![X29 : $i, X30 : $i]:
% 0.37/0.62         (~ (m1_pre_topc @ X29 @ X30)
% 0.37/0.62          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.37/0.62          | ~ (l1_pre_topc @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.62  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.62  thf(t5_connsp_2, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.37/0.62                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.37/0.62  thf('49', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.62          | ~ (v3_pre_topc @ X17 @ X18)
% 0.37/0.62          | ~ (r2_hidden @ X19 @ X17)
% 0.37/0.62          | (m1_connsp_2 @ X17 @ X18 @ X19)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.37/0.62          | ~ (l1_pre_topc @ X18)
% 0.37/0.62          | ~ (v2_pre_topc @ X18)
% 0.37/0.62          | (v2_struct_0 @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.37/0.62  thf('50', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.62  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.37/0.62  thf('54', plain,
% 0.37/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.62  thf(t16_tsep_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.37/0.62                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.37/0.62                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.62         (~ (m1_pre_topc @ X26 @ X27)
% 0.37/0.62          | ((X28) != (u1_struct_0 @ X26))
% 0.37/0.62          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.37/0.62          | ~ (m1_pre_topc @ X26 @ X27)
% 0.37/0.62          | (v3_pre_topc @ X28 @ X27)
% 0.37/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.37/0.62          | ~ (l1_pre_topc @ X27)
% 0.37/0.62          | ~ (v2_pre_topc @ X27))),
% 0.37/0.62      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.37/0.62  thf('56', plain,
% 0.37/0.62      (![X26 : $i, X27 : $i]:
% 0.37/0.62         (~ (v2_pre_topc @ X27)
% 0.37/0.62          | ~ (l1_pre_topc @ X27)
% 0.37/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.37/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.37/0.62          | (v3_pre_topc @ (u1_struct_0 @ X26) @ X27)
% 0.37/0.62          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.37/0.62          | ~ (m1_pre_topc @ X26 @ X27))),
% 0.37/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.37/0.62  thf('57', plain,
% 0.37/0.62      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.37/0.62        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.37/0.62        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.37/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | ~ (v2_pre_topc @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['54', '56'])).
% 0.37/0.62  thf('58', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('59', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('62', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.37/0.62      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('demod', [status(thm)], ['53', '62'])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['43', '63'])).
% 0.37/0.62  thf('65', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      (((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.37/0.62        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('clc', [status(thm)], ['64', '65'])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.37/0.62      inference('sup-', [status(thm)], ['42', '66'])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.62  thf(t7_connsp_2, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.37/0.62                    ( ![D:$i]:
% 0.37/0.62                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.37/0.62                          ( m1_subset_1 @
% 0.37/0.62                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.37/0.62                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.37/0.62          | (m1_connsp_2 @ (sk_D @ X25 @ X23 @ X24) @ X24 @ X23)
% 0.37/0.62          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.37/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.62          | ~ (l1_pre_topc @ X24)
% 0.37/0.62          | ~ (v2_pre_topc @ X24)
% 0.37/0.62          | (v2_struct_0 @ X24))),
% 0.37/0.62      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.37/0.62  thf('70', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.37/0.62             sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.62  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('73', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.37/0.62             sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.37/0.62  thf('74', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.37/0.62        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62           sk_B @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['67', '73'])).
% 0.37/0.62  thf('75', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('76', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62           sk_B @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['74', '75'])).
% 0.37/0.62  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('78', plain,
% 0.37/0.62      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B @ 
% 0.37/0.62         sk_E)
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('clc', [status(thm)], ['76', '77'])).
% 0.37/0.62  thf('79', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.37/0.62      inference('sup-', [status(thm)], ['42', '66'])).
% 0.37/0.62  thf('80', plain,
% 0.37/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.62  thf('81', plain,
% 0.37/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.37/0.62          | (r1_tarski @ (sk_D @ X25 @ X23 @ X24) @ X25)
% 0.37/0.62          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.37/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.62          | ~ (l1_pre_topc @ X24)
% 0.37/0.62          | ~ (v2_pre_topc @ X24)
% 0.37/0.62          | (v2_struct_0 @ X24))),
% 0.37/0.62      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.37/0.62  thf('82', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.37/0.62             (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.62  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('85', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.37/0.62             (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.37/0.62  thf('86', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.37/0.62        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62           (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['79', '85'])).
% 0.37/0.62  thf('87', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('88', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62           (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.62  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('90', plain,
% 0.37/0.62      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62         (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('clc', [status(thm)], ['88', '89'])).
% 0.37/0.62  thf('91', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.37/0.62      inference('sup-', [status(thm)], ['42', '66'])).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.62  thf('93', plain,
% 0.37/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.37/0.62          | (m1_subset_1 @ (sk_D @ X25 @ X23 @ X24) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.37/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.62          | ~ (l1_pre_topc @ X24)
% 0.37/0.62          | ~ (v2_pre_topc @ X24)
% 0.37/0.62          | (v2_struct_0 @ X24))),
% 0.37/0.62      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.37/0.62  thf('94', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['92', '93'])).
% 0.37/0.62  thf('95', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('97', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.62          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.37/0.62  thf('98', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.37/0.62        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['91', '97'])).
% 0.37/0.62  thf('99', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('100', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['98', '99'])).
% 0.37/0.62  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('102', plain,
% 0.37/0.62      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('clc', [status(thm)], ['100', '101'])).
% 0.37/0.62  thf('103', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.37/0.62        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('104', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.37/0.62      inference('split', [status(esa)], ['103'])).
% 0.37/0.62  thf('105', plain, (((sk_E) = (sk_F))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('106', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.37/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.37/0.62  thf('107', plain,
% 0.37/0.62      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.37/0.62        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('108', plain,
% 0.37/0.62      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.37/0.62       ~
% 0.37/0.62       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.37/0.62      inference('split', [status(esa)], ['107'])).
% 0.37/0.62  thf('109', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf('110', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('split', [status(esa)], ['103'])).
% 0.37/0.62  thf('111', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.62        (k1_zfmisc_1 @ 
% 0.37/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t64_tmap_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.62             ( l1_pre_topc @ B ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.62                 ( m1_subset_1 @
% 0.37/0.62                   C @ 
% 0.37/0.62                   ( k1_zfmisc_1 @
% 0.37/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.62               ( ![D:$i]:
% 0.37/0.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.62                   ( ![E:$i]:
% 0.37/0.62                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.62                       ( ![F:$i]:
% 0.37/0.62                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.62                           ( ( ( ( E ) = ( F ) ) & 
% 0.37/0.62                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.37/0.62                             ( r1_tmap_1 @
% 0.37/0.62                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('112', plain,
% 0.37/0.62      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X31)
% 0.37/0.62          | ~ (v2_pre_topc @ X31)
% 0.37/0.62          | ~ (l1_pre_topc @ X31)
% 0.37/0.62          | (v2_struct_0 @ X32)
% 0.37/0.62          | ~ (m1_pre_topc @ X32 @ X31)
% 0.37/0.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.37/0.62          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.37/0.62          | ((X36) != (X33))
% 0.37/0.62          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 0.37/0.62          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.37/0.62          | ~ (m1_subset_1 @ X35 @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.37/0.62          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.37/0.62          | ~ (v1_funct_1 @ X35)
% 0.37/0.62          | ~ (l1_pre_topc @ X34)
% 0.37/0.62          | ~ (v2_pre_topc @ X34)
% 0.37/0.62          | (v2_struct_0 @ X34))),
% 0.37/0.62      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.37/0.62  thf('113', plain,
% 0.37/0.62      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X34)
% 0.37/0.62          | ~ (v2_pre_topc @ X34)
% 0.37/0.62          | ~ (l1_pre_topc @ X34)
% 0.37/0.62          | ~ (v1_funct_1 @ X35)
% 0.37/0.62          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.37/0.62          | ~ (m1_subset_1 @ X35 @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.37/0.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.37/0.62          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 0.37/0.62          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.37/0.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.37/0.62          | ~ (m1_pre_topc @ X32 @ X31)
% 0.37/0.62          | (v2_struct_0 @ X32)
% 0.37/0.62          | ~ (l1_pre_topc @ X31)
% 0.37/0.62          | ~ (v2_pre_topc @ X31)
% 0.37/0.62          | (v2_struct_0 @ X31))),
% 0.37/0.62      inference('simplify', [status(thm)], ['112'])).
% 0.37/0.62  thf('114', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.62          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.37/0.62             X1)
% 0.37/0.62          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.62               (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62          | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['111', '113'])).
% 0.37/0.62  thf('115', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('117', plain,
% 0.37/0.62      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('118', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('121', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.62          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.37/0.62             X1)
% 0.37/0.62          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['114', '115', '116', '117', '118', '119', '120'])).
% 0.37/0.62  thf('122', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          ((v2_struct_0 @ sk_A)
% 0.37/0.62           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.37/0.62           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.62              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.37/0.62           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.37/0.62           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.62           | (v2_struct_0 @ X0)
% 0.37/0.62           | (v2_struct_0 @ sk_B)))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['110', '121'])).
% 0.37/0.62  thf('123', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('124', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          ((v2_struct_0 @ sk_A)
% 0.37/0.62           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.62              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.37/0.62           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.37/0.62           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.62           | (v2_struct_0 @ X0)
% 0.37/0.62           | (v2_struct_0 @ sk_B)))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('demod', [status(thm)], ['122', '123'])).
% 0.37/0.62  thf('125', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_D_1)
% 0.37/0.62         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.37/0.62         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.37/0.62         | (v2_struct_0 @ sk_A)))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['109', '124'])).
% 0.37/0.62  thf('126', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('127', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_D_1)
% 0.37/0.62         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.37/0.62         | (v2_struct_0 @ sk_A)))
% 0.37/0.62         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('demod', [status(thm)], ['125', '126'])).
% 0.37/0.62  thf('128', plain,
% 0.37/0.62      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.37/0.62      inference('split', [status(esa)], ['107'])).
% 0.37/0.62  thf('129', plain, (((sk_E) = (sk_F))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('130', plain,
% 0.37/0.62      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.37/0.62      inference('demod', [status(thm)], ['128', '129'])).
% 0.37/0.62  thf('131', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.37/0.62             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['127', '130'])).
% 0.37/0.62  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('133', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.37/0.62             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('clc', [status(thm)], ['131', '132'])).
% 0.37/0.62  thf('134', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('135', plain,
% 0.37/0.62      (((v2_struct_0 @ sk_D_1))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.37/0.62             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('clc', [status(thm)], ['133', '134'])).
% 0.37/0.62  thf('136', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('137', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.37/0.62       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.37/0.62      inference('sup-', [status(thm)], ['135', '136'])).
% 0.37/0.62  thf('138', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.37/0.62       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.37/0.62      inference('split', [status(esa)], ['103'])).
% 0.37/0.62  thf('139', plain,
% 0.37/0.62      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['108', '137', '138'])).
% 0.37/0.62  thf('140', plain,
% 0.37/0.62      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.62        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.37/0.62      inference('simpl_trail', [status(thm)], ['106', '139'])).
% 0.37/0.62  thf('141', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.62        (k1_zfmisc_1 @ 
% 0.37/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t65_tmap_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.62             ( l1_pre_topc @ B ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.62                 ( m1_subset_1 @
% 0.37/0.62                   C @ 
% 0.37/0.62                   ( k1_zfmisc_1 @
% 0.37/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.62               ( ![D:$i]:
% 0.37/0.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.62                   ( ![E:$i]:
% 0.37/0.62                     ( ( m1_subset_1 @
% 0.37/0.62                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.62                       ( ![F:$i]:
% 0.37/0.62                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.62                           ( ![G:$i]:
% 0.37/0.62                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.62                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.37/0.62                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.37/0.62                                   ( ( F ) = ( G ) ) ) =>
% 0.37/0.62                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.37/0.62                                   ( r1_tmap_1 @
% 0.37/0.62                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('142', plain,
% 0.37/0.62      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X37)
% 0.37/0.62          | ~ (v2_pre_topc @ X37)
% 0.37/0.62          | ~ (l1_pre_topc @ X37)
% 0.37/0.62          | (v2_struct_0 @ X38)
% 0.37/0.62          | ~ (m1_pre_topc @ X38 @ X37)
% 0.37/0.62          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.37/0.62          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.37/0.62          | ~ (m1_connsp_2 @ X40 @ X37 @ X39)
% 0.37/0.62          | ((X39) != (X41))
% 0.37/0.62          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.37/0.62               X41)
% 0.37/0.62          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X39)
% 0.37/0.62          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.37/0.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.37/0.62          | ~ (m1_subset_1 @ X43 @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.37/0.62          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.37/0.62          | ~ (v1_funct_1 @ X43)
% 0.37/0.62          | ~ (l1_pre_topc @ X42)
% 0.37/0.62          | ~ (v2_pre_topc @ X42)
% 0.37/0.62          | (v2_struct_0 @ X42))),
% 0.37/0.62      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.37/0.62  thf('143', plain,
% 0.37/0.62      (![X37 : $i, X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X42)
% 0.37/0.62          | ~ (v2_pre_topc @ X42)
% 0.37/0.62          | ~ (l1_pre_topc @ X42)
% 0.37/0.62          | ~ (v1_funct_1 @ X43)
% 0.37/0.62          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.37/0.62          | ~ (m1_subset_1 @ X43 @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.37/0.62          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.37/0.62          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.37/0.62          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X41)
% 0.37/0.62          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.37/0.62               X41)
% 0.37/0.62          | ~ (m1_connsp_2 @ X40 @ X37 @ X41)
% 0.37/0.62          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.37/0.62          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 0.37/0.62          | ~ (m1_pre_topc @ X38 @ X37)
% 0.37/0.62          | (v2_struct_0 @ X38)
% 0.37/0.62          | ~ (l1_pre_topc @ X37)
% 0.37/0.62          | ~ (v2_pre_topc @ X37)
% 0.37/0.62          | (v2_struct_0 @ X37))),
% 0.37/0.62      inference('simplify', [status(thm)], ['142'])).
% 0.37/0.62  thf('144', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.37/0.62          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.37/0.62          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.37/0.62          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.62               (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62          | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['141', '143'])).
% 0.37/0.62  thf('145', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('146', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('147', plain,
% 0.37/0.62      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('148', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('151', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.37/0.62          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.37/0.62          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.62               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.37/0.62          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['144', '145', '146', '147', '148', '149', '150'])).
% 0.37/0.62  thf('152', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_A)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.37/0.62          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.37/0.62          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_D_1)
% 0.37/0.62          | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['140', '151'])).
% 0.37/0.62  thf('153', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf('154', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('155', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('156', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_A)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.37/0.62          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | (v2_struct_0 @ sk_D_1)
% 0.37/0.62          | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 0.37/0.62  thf('157', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_B)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62             (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62             sk_B @ sk_E)
% 0.37/0.62        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['102', '156'])).
% 0.37/0.62  thf('158', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62             sk_B @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | (v2_struct_0 @ sk_B)
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['90', '157'])).
% 0.37/0.62  thf('159', plain,
% 0.37/0.62      (((v2_struct_0 @ sk_B)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.37/0.62             sk_B @ sk_E)
% 0.37/0.62        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['158'])).
% 0.37/0.62  thf('160', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['78', '159'])).
% 0.37/0.62  thf('161', plain,
% 0.37/0.62      (((v2_struct_0 @ sk_B)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['160'])).
% 0.37/0.62  thf('162', plain,
% 0.37/0.62      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.37/0.62         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.37/0.62      inference('split', [status(esa)], ['107'])).
% 0.37/0.62  thf('163', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['108', '137'])).
% 0.37/0.62  thf('164', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.37/0.62      inference('simpl_trail', [status(thm)], ['162', '163'])).
% 0.37/0.62  thf('165', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (v2_struct_0 @ sk_D_1)
% 0.37/0.62        | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['161', '164'])).
% 0.37/0.62  thf('166', plain,
% 0.37/0.62      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['20', '28'])).
% 0.37/0.62  thf(t5_subset, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.62  thf('167', plain,
% 0.37/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.62          | ~ (v1_xboole_0 @ X4)
% 0.37/0.62          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.62  thf('168', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['166', '167'])).
% 0.37/0.62  thf('169', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_D_1)
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['165', '168'])).
% 0.37/0.62  thf('170', plain,
% 0.37/0.62      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['39', '169'])).
% 0.37/0.62  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('172', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.37/0.62      inference('clc', [status(thm)], ['170', '171'])).
% 0.37/0.62  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('174', plain, ((v2_struct_0 @ sk_D_1)),
% 0.37/0.62      inference('clc', [status(thm)], ['172', '173'])).
% 0.37/0.62  thf('175', plain, ($false), inference('demod', [status(thm)], ['0', '174'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
