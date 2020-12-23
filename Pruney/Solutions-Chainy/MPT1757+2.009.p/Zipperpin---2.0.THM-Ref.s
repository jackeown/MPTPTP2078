%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QHkgB7c3sA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:54 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  203 (1133 expanded)
%              Number of leaves         :   38 ( 334 expanded)
%              Depth                    :   22
%              Number of atoms          : 2244 (34078 expanded)
%              Number of equality atoms :   11 ( 504 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_connsp_2 @ ( sk_C_1 @ X18 @ X17 ) @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ( ( m1_connsp_2 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_connsp_2 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_connsp_2 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_connsp_2 @ X16 @ X14 @ X15 ) ) ),
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
    m1_subset_1 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_connsp_2 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C_1 @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
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
      | ( r2_hidden @ X0 @ ( sk_C_1 @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_E @ ( sk_C_1 @ sk_E @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('37',plain,
    ( ( r2_hidden @ sk_E @ ( sk_C_1 @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_E @ ( sk_C_1 @ sk_E @ sk_D_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ ( sk_C_1 @ sk_E @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

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

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( sk_D @ X24 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

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

thf('57',plain,(
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

thf('58',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X26 ) @ X27 )
      | ~ ( v1_tsep_1 @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['55','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(split,[status(esa)],['71'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('80',plain,(
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

thf('81',plain,(
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
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_3 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C_3 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('97',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(split,[status(esa)],['71'])).

thf('107',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['76','105','106'])).

thf('108',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['74','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('110',plain,(
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

thf('111',plain,(
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
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_3 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C_3 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('122',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('128',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ( r1_tarski @ ( sk_D @ X24 @ X22 @ X23 ) @ X22 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['126','134'])).

thf('136',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('137',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('142',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ( m1_connsp_2 @ ( sk_D @ X24 @ X22 @ X23 ) @ X23 @ X24 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','148'])).

thf('150',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('151',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','139','153'])).

thf('155',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(split,[status(esa)],['75'])).

thf('156',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['76','105'])).

thf('157',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['154','157'])).

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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QHkgB7c3sA
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.84  % Solved by: fo/fo7.sh
% 0.64/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.84  % done 455 iterations in 0.358s
% 0.64/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.84  % SZS output start Refutation
% 0.64/0.84  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.64/0.84  thf(sk_E_type, type, sk_E: $i).
% 0.64/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.64/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.84  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.64/0.84  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.64/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.84  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.64/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.64/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.84  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.64/0.84  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.64/0.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.64/0.84  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.64/0.84  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.64/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.64/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.84  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.64/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.84  thf(sk_F_type, type, sk_F: $i).
% 0.64/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.64/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.64/0.84  thf(t67_tmap_1, conjecture,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.64/0.84             ( l1_pre_topc @ B ) ) =>
% 0.64/0.84           ( ![C:$i]:
% 0.64/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.64/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.64/0.84                 ( m1_subset_1 @
% 0.64/0.84                   C @ 
% 0.64/0.84                   ( k1_zfmisc_1 @
% 0.64/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.64/0.84               ( ![D:$i]:
% 0.64/0.84                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.64/0.84                     ( m1_pre_topc @ D @ B ) ) =>
% 0.64/0.84                   ( ![E:$i]:
% 0.64/0.84                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.64/0.84                       ( ![F:$i]:
% 0.64/0.84                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.64/0.84                           ( ( ( E ) = ( F ) ) =>
% 0.64/0.84                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.64/0.84                               ( r1_tmap_1 @
% 0.64/0.84                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.84    (~( ![A:$i]:
% 0.64/0.84        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.64/0.84            ( l1_pre_topc @ A ) ) =>
% 0.64/0.84          ( ![B:$i]:
% 0.64/0.84            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.64/0.84                ( l1_pre_topc @ B ) ) =>
% 0.64/0.84              ( ![C:$i]:
% 0.64/0.84                ( ( ( v1_funct_1 @ C ) & 
% 0.64/0.84                    ( v1_funct_2 @
% 0.64/0.84                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.64/0.84                    ( m1_subset_1 @
% 0.64/0.84                      C @ 
% 0.64/0.84                      ( k1_zfmisc_1 @
% 0.64/0.84                        ( k2_zfmisc_1 @
% 0.64/0.84                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.64/0.84                  ( ![D:$i]:
% 0.64/0.84                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.64/0.84                        ( m1_pre_topc @ D @ B ) ) =>
% 0.64/0.84                      ( ![E:$i]:
% 0.64/0.84                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.64/0.84                          ( ![F:$i]:
% 0.64/0.84                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.64/0.84                              ( ( ( E ) = ( F ) ) =>
% 0.64/0.84                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.64/0.84                                  ( r1_tmap_1 @
% 0.64/0.84                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.64/0.84    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.64/0.84  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('2', plain, (((sk_E) = (sk_F))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.84  thf(existence_m1_connsp_2, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.64/0.84         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.84       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.64/0.84  thf('4', plain,
% 0.64/0.84      (![X17 : $i, X18 : $i]:
% 0.64/0.84         (~ (l1_pre_topc @ X17)
% 0.64/0.84          | ~ (v2_pre_topc @ X17)
% 0.64/0.84          | (v2_struct_0 @ X17)
% 0.64/0.84          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.64/0.84          | (m1_connsp_2 @ (sk_C_1 @ X18 @ X17) @ X17 @ X18))),
% 0.64/0.84      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.64/0.84  thf('5', plain,
% 0.64/0.84      (((m1_connsp_2 @ (sk_C_1 @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.64/0.84        | (v2_struct_0 @ sk_D_1)
% 0.64/0.84        | ~ (v2_pre_topc @ sk_D_1)
% 0.64/0.84        | ~ (l1_pre_topc @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['3', '4'])).
% 0.64/0.84  thf('6', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(cc1_pre_topc, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.64/0.84  thf('7', plain,
% 0.64/0.84      (![X7 : $i, X8 : $i]:
% 0.64/0.84         (~ (m1_pre_topc @ X7 @ X8)
% 0.64/0.84          | (v2_pre_topc @ X7)
% 0.64/0.84          | ~ (l1_pre_topc @ X8)
% 0.64/0.84          | ~ (v2_pre_topc @ X8))),
% 0.64/0.84      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.64/0.84  thf('8', plain,
% 0.64/0.84      ((~ (v2_pre_topc @ sk_B)
% 0.64/0.84        | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84        | (v2_pre_topc @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.64/0.84  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('11', plain, ((v2_pre_topc @ sk_D_1)),
% 0.64/0.84      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.64/0.84  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(dt_m1_pre_topc, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( l1_pre_topc @ A ) =>
% 0.64/0.84       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.64/0.84  thf('13', plain,
% 0.64/0.84      (![X9 : $i, X10 : $i]:
% 0.64/0.84         (~ (m1_pre_topc @ X9 @ X10)
% 0.64/0.84          | (l1_pre_topc @ X9)
% 0.64/0.84          | ~ (l1_pre_topc @ X10))),
% 0.64/0.84      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.64/0.84  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.84  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.64/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.64/0.84  thf('17', plain,
% 0.64/0.84      (((m1_connsp_2 @ (sk_C_1 @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.64/0.84        | (v2_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.64/0.84  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('19', plain, ((m1_connsp_2 @ (sk_C_1 @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.64/0.84      inference('clc', [status(thm)], ['17', '18'])).
% 0.64/0.84  thf('20', plain, ((m1_connsp_2 @ (sk_C_1 @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.64/0.84      inference('clc', [status(thm)], ['17', '18'])).
% 0.64/0.84  thf('21', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.84  thf(dt_m1_connsp_2, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.64/0.84         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.84       ( ![C:$i]:
% 0.64/0.84         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.64/0.84           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.64/0.84  thf('22', plain,
% 0.64/0.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.84         (~ (l1_pre_topc @ X14)
% 0.64/0.84          | ~ (v2_pre_topc @ X14)
% 0.64/0.84          | (v2_struct_0 @ X14)
% 0.64/0.84          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.64/0.84          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.64/0.84          | ~ (m1_connsp_2 @ X16 @ X14 @ X15))),
% 0.64/0.84      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.64/0.84  thf('23', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.64/0.84          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.64/0.84          | (v2_struct_0 @ sk_D_1)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_D_1)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.84  thf('24', plain, ((v2_pre_topc @ sk_D_1)),
% 0.64/0.84      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.64/0.84  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.64/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.64/0.84  thf('26', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.64/0.84          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.64/0.84          | (v2_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.64/0.84  thf('27', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('28', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.64/0.84          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.64/0.84      inference('clc', [status(thm)], ['26', '27'])).
% 0.64/0.84  thf('29', plain,
% 0.64/0.84      ((m1_subset_1 @ (sk_C_1 @ sk_E @ sk_D_1) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['20', '28'])).
% 0.64/0.84  thf(t6_connsp_2, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.84           ( ![C:$i]:
% 0.64/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.64/0.84               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.64/0.84  thf('30', plain,
% 0.64/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.64/0.84          | ~ (m1_connsp_2 @ X19 @ X20 @ X21)
% 0.64/0.84          | (r2_hidden @ X21 @ X19)
% 0.64/0.84          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.64/0.84          | ~ (l1_pre_topc @ X20)
% 0.64/0.84          | ~ (v2_pre_topc @ X20)
% 0.64/0.84          | (v2_struct_0 @ X20))),
% 0.64/0.84      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.64/0.84  thf('31', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_D_1)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_D_1)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_D_1)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (r2_hidden @ X0 @ (sk_C_1 @ sk_E @ sk_D_1))
% 0.64/0.84          | ~ (m1_connsp_2 @ (sk_C_1 @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.64/0.84  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.64/0.84      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.64/0.84  thf('33', plain, ((l1_pre_topc @ sk_D_1)),
% 0.64/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.64/0.84  thf('34', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_D_1)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (r2_hidden @ X0 @ (sk_C_1 @ sk_E @ sk_D_1))
% 0.64/0.84          | ~ (m1_connsp_2 @ (sk_C_1 @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.64/0.84      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.64/0.84  thf('35', plain,
% 0.64/0.84      (((r2_hidden @ sk_E @ (sk_C_1 @ sk_E @ sk_D_1))
% 0.64/0.84        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84        | (v2_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['19', '34'])).
% 0.64/0.84  thf('36', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.84  thf('37', plain,
% 0.64/0.84      (((r2_hidden @ sk_E @ (sk_C_1 @ sk_E @ sk_D_1)) | (v2_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['35', '36'])).
% 0.64/0.84  thf('38', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('39', plain, ((r2_hidden @ sk_E @ (sk_C_1 @ sk_E @ sk_D_1))),
% 0.64/0.84      inference('clc', [status(thm)], ['37', '38'])).
% 0.64/0.84  thf('40', plain,
% 0.64/0.84      ((m1_subset_1 @ (sk_C_1 @ sk_E @ sk_D_1) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['20', '28'])).
% 0.64/0.84  thf(t3_subset, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.84  thf('41', plain,
% 0.64/0.84      (![X4 : $i, X5 : $i]:
% 0.64/0.84         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.64/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.84  thf('42', plain,
% 0.64/0.84      ((r1_tarski @ (sk_C_1 @ sk_E @ sk_D_1) @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.64/0.84  thf(d3_tarski, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.64/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.64/0.84  thf('43', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.64/0.84          | (r2_hidden @ X0 @ X2)
% 0.64/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.64/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.84  thf('44', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (sk_C_1 @ sk_E @ sk_D_1)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['42', '43'])).
% 0.64/0.84  thf('45', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['39', '44'])).
% 0.64/0.84  thf('46', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(t1_tsep_1, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( l1_pre_topc @ A ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( m1_pre_topc @ B @ A ) =>
% 0.64/0.84           ( m1_subset_1 @
% 0.64/0.84             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.64/0.84  thf('47', plain,
% 0.64/0.84      (![X29 : $i, X30 : $i]:
% 0.64/0.84         (~ (m1_pre_topc @ X29 @ X30)
% 0.64/0.84          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.64/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.64/0.84          | ~ (l1_pre_topc @ X30))),
% 0.64/0.84      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.64/0.84  thf('48', plain,
% 0.64/0.84      ((~ (l1_pre_topc @ sk_B)
% 0.64/0.84        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.64/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.64/0.84  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('50', plain,
% 0.64/0.84      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.64/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.64/0.84  thf(t9_connsp_2, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.84           ( ( v3_pre_topc @ B @ A ) <=>
% 0.64/0.84             ( ![C:$i]:
% 0.64/0.84               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.64/0.84                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.64/0.84                      ( ![D:$i]:
% 0.64/0.84                        ( ( m1_subset_1 @
% 0.64/0.84                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.84                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.64/0.84                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.84  thf('51', plain,
% 0.64/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.64/0.84          | ~ (v3_pre_topc @ X22 @ X23)
% 0.64/0.84          | (m1_subset_1 @ (sk_D @ X24 @ X22 @ X23) @ 
% 0.64/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.64/0.84          | ~ (r2_hidden @ X24 @ X22)
% 0.64/0.84          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.64/0.84          | ~ (l1_pre_topc @ X23)
% 0.64/0.84          | ~ (v2_pre_topc @ X23)
% 0.64/0.84          | (v2_struct_0 @ X23))),
% 0.64/0.84      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.64/0.84  thf('52', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_B)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['50', '51'])).
% 0.64/0.84  thf('53', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('55', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.64/0.84  thf('56', plain,
% 0.64/0.84      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.64/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.64/0.84  thf(t16_tsep_1, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( m1_pre_topc @ B @ A ) =>
% 0.64/0.84           ( ![C:$i]:
% 0.64/0.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.84               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.64/0.84                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.64/0.84                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.64/0.84  thf('57', plain,
% 0.64/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.64/0.84         (~ (m1_pre_topc @ X26 @ X27)
% 0.64/0.84          | ((X28) != (u1_struct_0 @ X26))
% 0.64/0.84          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.64/0.84          | ~ (m1_pre_topc @ X26 @ X27)
% 0.64/0.84          | (v3_pre_topc @ X28 @ X27)
% 0.64/0.84          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.64/0.84          | ~ (l1_pre_topc @ X27)
% 0.64/0.84          | ~ (v2_pre_topc @ X27))),
% 0.64/0.84      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.64/0.84  thf('58', plain,
% 0.64/0.84      (![X26 : $i, X27 : $i]:
% 0.64/0.84         (~ (v2_pre_topc @ X27)
% 0.64/0.84          | ~ (l1_pre_topc @ X27)
% 0.64/0.84          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.64/0.84               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.64/0.84          | (v3_pre_topc @ (u1_struct_0 @ X26) @ X27)
% 0.64/0.84          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.64/0.84          | ~ (m1_pre_topc @ X26 @ X27))),
% 0.64/0.84      inference('simplify', [status(thm)], ['57'])).
% 0.64/0.84  thf('59', plain,
% 0.64/0.84      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.64/0.84        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.64/0.84        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.64/0.84        | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84        | ~ (v2_pre_topc @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['56', '58'])).
% 0.64/0.84  thf('60', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('61', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('63', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('64', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.64/0.84      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.64/0.84  thf('65', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.64/0.84      inference('demod', [status(thm)], ['55', '64'])).
% 0.64/0.84  thf('66', plain,
% 0.64/0.84      (((m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.64/0.84        | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['45', '65'])).
% 0.64/0.84  thf('67', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('68', plain,
% 0.64/0.84      (((m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84        | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['66', '67'])).
% 0.64/0.84  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('70', plain,
% 0.64/0.84      ((m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.64/0.84      inference('clc', [status(thm)], ['68', '69'])).
% 0.64/0.84  thf('71', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)
% 0.64/0.84        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('72', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)))),
% 0.64/0.84      inference('split', [status(esa)], ['71'])).
% 0.64/0.84  thf('73', plain, (((sk_E) = (sk_F))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('74', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_E))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)))),
% 0.64/0.84      inference('demod', [status(thm)], ['72', '73'])).
% 0.64/0.84  thf('75', plain,
% 0.64/0.84      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)
% 0.64/0.84        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('76', plain,
% 0.64/0.84      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)) | 
% 0.64/0.84       ~
% 0.64/0.84       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F))),
% 0.64/0.84      inference('split', [status(esa)], ['75'])).
% 0.64/0.84  thf('77', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.84  thf('78', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('split', [status(esa)], ['71'])).
% 0.64/0.84  thf('79', plain,
% 0.64/0.84      ((m1_subset_1 @ sk_C_3 @ 
% 0.64/0.84        (k1_zfmisc_1 @ 
% 0.64/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(t64_tmap_1, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.64/0.84             ( l1_pre_topc @ B ) ) =>
% 0.64/0.84           ( ![C:$i]:
% 0.64/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.64/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.64/0.84                 ( m1_subset_1 @
% 0.64/0.84                   C @ 
% 0.64/0.84                   ( k1_zfmisc_1 @
% 0.64/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.64/0.84               ( ![D:$i]:
% 0.64/0.84                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.64/0.84                   ( ![E:$i]:
% 0.64/0.84                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.64/0.84                       ( ![F:$i]:
% 0.64/0.84                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.64/0.84                           ( ( ( ( E ) = ( F ) ) & 
% 0.64/0.84                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.64/0.84                             ( r1_tmap_1 @
% 0.64/0.84                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.84  thf('80', plain,
% 0.64/0.84      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.64/0.84         ((v2_struct_0 @ X31)
% 0.64/0.84          | ~ (v2_pre_topc @ X31)
% 0.64/0.84          | ~ (l1_pre_topc @ X31)
% 0.64/0.84          | (v2_struct_0 @ X32)
% 0.64/0.84          | ~ (m1_pre_topc @ X32 @ X31)
% 0.64/0.84          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.64/0.84          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.64/0.84          | ((X36) != (X33))
% 0.64/0.84          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 0.64/0.84          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.64/0.84          | ~ (m1_subset_1 @ X35 @ 
% 0.64/0.84               (k1_zfmisc_1 @ 
% 0.64/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.64/0.84          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.64/0.84          | ~ (v1_funct_1 @ X35)
% 0.64/0.84          | ~ (l1_pre_topc @ X34)
% 0.64/0.84          | ~ (v2_pre_topc @ X34)
% 0.64/0.84          | (v2_struct_0 @ X34))),
% 0.64/0.84      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.64/0.84  thf('81', plain,
% 0.64/0.84      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.64/0.84         ((v2_struct_0 @ X34)
% 0.64/0.84          | ~ (v2_pre_topc @ X34)
% 0.64/0.84          | ~ (l1_pre_topc @ X34)
% 0.64/0.84          | ~ (v1_funct_1 @ X35)
% 0.64/0.84          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.64/0.84          | ~ (m1_subset_1 @ X35 @ 
% 0.64/0.84               (k1_zfmisc_1 @ 
% 0.64/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.64/0.84          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.64/0.84          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 0.64/0.84          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.64/0.84          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.64/0.84          | ~ (m1_pre_topc @ X32 @ X31)
% 0.64/0.84          | (v2_struct_0 @ X32)
% 0.64/0.84          | ~ (l1_pre_topc @ X31)
% 0.64/0.84          | ~ (v2_pre_topc @ X31)
% 0.64/0.84          | (v2_struct_0 @ X31))),
% 0.64/0.84      inference('simplify', [status(thm)], ['80'])).
% 0.64/0.84  thf('82', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_B)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84          | (v2_struct_0 @ X0)
% 0.64/0.84          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.64/0.84          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0) @ 
% 0.64/0.84             X1)
% 0.64/0.84          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (v1_funct_2 @ sk_C_3 @ (u1_struct_0 @ sk_B) @ 
% 0.64/0.84               (u1_struct_0 @ sk_A))
% 0.64/0.84          | ~ (v1_funct_1 @ sk_C_3)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_A)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_A)
% 0.64/0.84          | (v2_struct_0 @ sk_A))),
% 0.64/0.84      inference('sup-', [status(thm)], ['79', '81'])).
% 0.64/0.84  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('85', plain,
% 0.64/0.84      ((v1_funct_2 @ sk_C_3 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('86', plain, ((v1_funct_1 @ sk_C_3)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('89', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | (v2_struct_0 @ X0)
% 0.64/0.84          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.64/0.84          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0) @ 
% 0.64/0.84             X1)
% 0.64/0.84          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | (v2_struct_0 @ sk_A))),
% 0.64/0.84      inference('demod', [status(thm)],
% 0.64/0.84                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.64/0.84  thf('90', plain,
% 0.64/0.84      ((![X0 : $i]:
% 0.64/0.84          ((v2_struct_0 @ sk_A)
% 0.64/0.84           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.64/0.84           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.64/0.84              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0) @ sk_E)
% 0.64/0.84           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.64/0.84           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.64/0.84           | (v2_struct_0 @ X0)
% 0.64/0.84           | (v2_struct_0 @ sk_B)))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['78', '89'])).
% 0.64/0.84  thf('91', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('92', plain,
% 0.64/0.84      ((![X0 : $i]:
% 0.64/0.84          ((v2_struct_0 @ sk_A)
% 0.64/0.84           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.64/0.84              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0) @ sk_E)
% 0.64/0.84           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.64/0.84           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.64/0.84           | (v2_struct_0 @ X0)
% 0.64/0.84           | (v2_struct_0 @ sk_B)))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('demod', [status(thm)], ['90', '91'])).
% 0.64/0.84  thf('93', plain,
% 0.64/0.84      ((((v2_struct_0 @ sk_B)
% 0.64/0.84         | (v2_struct_0 @ sk_D_1)
% 0.64/0.84         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.64/0.84         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_E)
% 0.64/0.84         | (v2_struct_0 @ sk_A)))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['77', '92'])).
% 0.64/0.84  thf('94', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('95', plain,
% 0.64/0.84      ((((v2_struct_0 @ sk_B)
% 0.64/0.84         | (v2_struct_0 @ sk_D_1)
% 0.64/0.84         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_E)
% 0.64/0.84         | (v2_struct_0 @ sk_A)))
% 0.64/0.84         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('demod', [status(thm)], ['93', '94'])).
% 0.64/0.84  thf('96', plain,
% 0.64/0.84      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)))),
% 0.64/0.84      inference('split', [status(esa)], ['75'])).
% 0.64/0.84  thf('97', plain, (((sk_E) = (sk_F))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('98', plain,
% 0.64/0.84      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_E))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)))),
% 0.64/0.84      inference('demod', [status(thm)], ['96', '97'])).
% 0.64/0.84  thf('99', plain,
% 0.64/0.84      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)) & 
% 0.64/0.84             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['95', '98'])).
% 0.64/0.84  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('101', plain,
% 0.64/0.84      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)) & 
% 0.64/0.84             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('clc', [status(thm)], ['99', '100'])).
% 0.64/0.84  thf('102', plain, (~ (v2_struct_0 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('103', plain,
% 0.64/0.84      (((v2_struct_0 @ sk_D_1))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)) & 
% 0.64/0.84             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('clc', [status(thm)], ['101', '102'])).
% 0.64/0.84  thf('104', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('105', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)) | 
% 0.64/0.84       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))),
% 0.64/0.84      inference('sup-', [status(thm)], ['103', '104'])).
% 0.64/0.84  thf('106', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F)) | 
% 0.64/0.84       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))),
% 0.64/0.84      inference('split', [status(esa)], ['71'])).
% 0.64/0.84  thf('107', plain,
% 0.64/0.84      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_F))),
% 0.64/0.84      inference('sat_resolution*', [status(thm)], ['76', '105', '106'])).
% 0.64/0.84  thf('108', plain,
% 0.64/0.84      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.64/0.84        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_D_1) @ sk_E)),
% 0.64/0.84      inference('simpl_trail', [status(thm)], ['74', '107'])).
% 0.64/0.84  thf('109', plain,
% 0.64/0.84      ((m1_subset_1 @ sk_C_3 @ 
% 0.64/0.84        (k1_zfmisc_1 @ 
% 0.64/0.84         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(t65_tmap_1, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.64/0.84             ( l1_pre_topc @ B ) ) =>
% 0.64/0.84           ( ![C:$i]:
% 0.64/0.84             ( ( ( v1_funct_1 @ C ) & 
% 0.64/0.84                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.64/0.84                 ( m1_subset_1 @
% 0.64/0.84                   C @ 
% 0.64/0.84                   ( k1_zfmisc_1 @
% 0.64/0.84                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.64/0.84               ( ![D:$i]:
% 0.64/0.84                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.64/0.84                   ( ![E:$i]:
% 0.64/0.84                     ( ( m1_subset_1 @
% 0.64/0.84                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.64/0.84                       ( ![F:$i]:
% 0.64/0.84                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.64/0.84                           ( ![G:$i]:
% 0.64/0.84                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.64/0.84                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.64/0.84                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.64/0.84                                   ( ( F ) = ( G ) ) ) =>
% 0.64/0.84                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.64/0.84                                   ( r1_tmap_1 @
% 0.64/0.84                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.84  thf('110', plain,
% 0.64/0.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.64/0.84         ((v2_struct_0 @ X37)
% 0.64/0.84          | ~ (v2_pre_topc @ X37)
% 0.64/0.84          | ~ (l1_pre_topc @ X37)
% 0.64/0.84          | (v2_struct_0 @ X38)
% 0.64/0.84          | ~ (m1_pre_topc @ X38 @ X37)
% 0.64/0.84          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.64/0.84          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.64/0.84          | ~ (m1_connsp_2 @ X40 @ X37 @ X39)
% 0.64/0.84          | ((X39) != (X41))
% 0.64/0.84          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.64/0.84               X41)
% 0.64/0.84          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X39)
% 0.64/0.84          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.64/0.84          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.64/0.84          | ~ (m1_subset_1 @ X43 @ 
% 0.64/0.84               (k1_zfmisc_1 @ 
% 0.64/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.64/0.84          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.64/0.84          | ~ (v1_funct_1 @ X43)
% 0.64/0.84          | ~ (l1_pre_topc @ X42)
% 0.64/0.84          | ~ (v2_pre_topc @ X42)
% 0.64/0.84          | (v2_struct_0 @ X42))),
% 0.64/0.84      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.64/0.84  thf('111', plain,
% 0.64/0.84      (![X37 : $i, X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.64/0.84         ((v2_struct_0 @ X42)
% 0.64/0.84          | ~ (v2_pre_topc @ X42)
% 0.64/0.84          | ~ (l1_pre_topc @ X42)
% 0.64/0.84          | ~ (v1_funct_1 @ X43)
% 0.64/0.84          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.64/0.84          | ~ (m1_subset_1 @ X43 @ 
% 0.64/0.84               (k1_zfmisc_1 @ 
% 0.64/0.84                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.64/0.84          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.64/0.84          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.64/0.84          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X41)
% 0.64/0.84          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.64/0.84               X41)
% 0.64/0.84          | ~ (m1_connsp_2 @ X40 @ X37 @ X41)
% 0.64/0.84          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.64/0.84          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 0.64/0.84          | ~ (m1_pre_topc @ X38 @ X37)
% 0.64/0.84          | (v2_struct_0 @ X38)
% 0.64/0.84          | ~ (l1_pre_topc @ X37)
% 0.64/0.84          | ~ (v2_pre_topc @ X37)
% 0.64/0.84          | (v2_struct_0 @ X37))),
% 0.64/0.84      inference('simplify', [status(thm)], ['110'])).
% 0.64/0.84  thf('112', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_B)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84          | (v2_struct_0 @ X0)
% 0.64/0.84          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.64/0.84          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.64/0.84          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0) @ X1)
% 0.64/0.84          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.64/0.84          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84          | ~ (v1_funct_2 @ sk_C_3 @ (u1_struct_0 @ sk_B) @ 
% 0.64/0.84               (u1_struct_0 @ sk_A))
% 0.64/0.84          | ~ (v1_funct_1 @ sk_C_3)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_A)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_A)
% 0.64/0.84          | (v2_struct_0 @ sk_A))),
% 0.64/0.84      inference('sup-', [status(thm)], ['109', '111'])).
% 0.64/0.84  thf('113', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('115', plain,
% 0.64/0.84      ((v1_funct_2 @ sk_C_3 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('116', plain, ((v1_funct_1 @ sk_C_3)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('119', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | (v2_struct_0 @ X0)
% 0.64/0.84          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.64/0.84          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.64/0.84          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.64/0.84               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X0) @ X1)
% 0.64/0.84          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ X1)
% 0.64/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.64/0.84          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84          | (v2_struct_0 @ sk_A))),
% 0.64/0.84      inference('demod', [status(thm)],
% 0.64/0.84                ['112', '113', '114', '115', '116', '117', '118'])).
% 0.64/0.84  thf('120', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_A)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)
% 0.64/0.84          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.64/0.84          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.64/0.84          | (v2_struct_0 @ sk_D_1)
% 0.64/0.84          | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['108', '119'])).
% 0.64/0.84  thf('121', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.84  thf('122', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('123', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('124', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_A)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.64/0.84          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)
% 0.64/0.84          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.64/0.84          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (v2_struct_0 @ sk_D_1)
% 0.64/0.84          | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.64/0.84  thf('125', plain,
% 0.64/0.84      (((v2_struct_0 @ sk_B)
% 0.64/0.84        | (v2_struct_0 @ sk_D_1)
% 0.64/0.84        | ~ (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (u1_struct_0 @ sk_D_1))
% 0.64/0.84        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             sk_B @ sk_E)
% 0.64/0.84        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)
% 0.64/0.84        | (v2_struct_0 @ sk_A))),
% 0.64/0.84      inference('sup-', [status(thm)], ['70', '124'])).
% 0.64/0.84  thf('126', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('127', plain,
% 0.64/0.84      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.64/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.64/0.84  thf('128', plain,
% 0.64/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.64/0.84          | ~ (v3_pre_topc @ X22 @ X23)
% 0.64/0.84          | (r1_tarski @ (sk_D @ X24 @ X22 @ X23) @ X22)
% 0.64/0.84          | ~ (r2_hidden @ X24 @ X22)
% 0.64/0.84          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.64/0.84          | ~ (l1_pre_topc @ X23)
% 0.64/0.84          | ~ (v2_pre_topc @ X23)
% 0.64/0.84          | (v2_struct_0 @ X23))),
% 0.64/0.84      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.64/0.84  thf('129', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_B)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['127', '128'])).
% 0.64/0.84  thf('130', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('132', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.64/0.84  thf('133', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.64/0.84      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.64/0.84  thf('134', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             (u1_struct_0 @ sk_D_1)))),
% 0.64/0.84      inference('demod', [status(thm)], ['132', '133'])).
% 0.64/0.84  thf('135', plain,
% 0.64/0.84      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84         (u1_struct_0 @ sk_D_1))
% 0.64/0.84        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84        | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['126', '134'])).
% 0.64/0.84  thf('136', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['39', '44'])).
% 0.64/0.84  thf('137', plain,
% 0.64/0.84      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84         (u1_struct_0 @ sk_D_1))
% 0.64/0.84        | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['135', '136'])).
% 0.64/0.84  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('139', plain,
% 0.64/0.84      ((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84        (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('clc', [status(thm)], ['137', '138'])).
% 0.64/0.84  thf('140', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('141', plain,
% 0.64/0.84      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.64/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.64/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.64/0.84  thf('142', plain,
% 0.64/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.64/0.84          | ~ (v3_pre_topc @ X22 @ X23)
% 0.64/0.84          | (m1_connsp_2 @ (sk_D @ X24 @ X22 @ X23) @ X23 @ X24)
% 0.64/0.84          | ~ (r2_hidden @ X24 @ X22)
% 0.64/0.84          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.64/0.84          | ~ (l1_pre_topc @ X23)
% 0.64/0.84          | ~ (v2_pre_topc @ X23)
% 0.64/0.84          | (v2_struct_0 @ X23))),
% 0.64/0.84      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.64/0.84  thf('143', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (v2_pre_topc @ sk_B)
% 0.64/0.84          | ~ (l1_pre_topc @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             sk_B @ X0)
% 0.64/0.84          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['141', '142'])).
% 0.64/0.84  thf('144', plain, ((v2_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('145', plain, ((l1_pre_topc @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('146', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             sk_B @ X0)
% 0.64/0.84          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.64/0.84  thf('147', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.64/0.84      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.64/0.84  thf('148', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((v2_struct_0 @ sk_B)
% 0.64/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.64/0.84          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.64/0.84             sk_B @ X0))),
% 0.64/0.84      inference('demod', [status(thm)], ['146', '147'])).
% 0.64/0.84  thf('149', plain,
% 0.64/0.84      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.64/0.84         sk_E)
% 0.64/0.84        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.64/0.84        | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['140', '148'])).
% 0.64/0.84  thf('150', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['39', '44'])).
% 0.64/0.84  thf('151', plain,
% 0.64/0.84      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.64/0.84         sk_E)
% 0.64/0.84        | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('demod', [status(thm)], ['149', '150'])).
% 0.64/0.84  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('153', plain,
% 0.64/0.84      ((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.64/0.84        sk_E)),
% 0.64/0.84      inference('clc', [status(thm)], ['151', '152'])).
% 0.64/0.84  thf('154', plain,
% 0.64/0.84      (((v2_struct_0 @ sk_B)
% 0.64/0.84        | (v2_struct_0 @ sk_D_1)
% 0.64/0.84        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)
% 0.64/0.84        | (v2_struct_0 @ sk_A))),
% 0.64/0.84      inference('demod', [status(thm)], ['125', '139', '153'])).
% 0.64/0.84  thf('155', plain,
% 0.64/0.84      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))
% 0.64/0.84         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)))),
% 0.64/0.84      inference('split', [status(esa)], ['75'])).
% 0.64/0.84  thf('156', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E))),
% 0.64/0.84      inference('sat_resolution*', [status(thm)], ['76', '105'])).
% 0.64/0.84  thf('157', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_3 @ sk_E)),
% 0.64/0.84      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 0.64/0.84  thf('158', plain,
% 0.64/0.84      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['154', '157'])).
% 0.64/0.84  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('160', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.64/0.84      inference('clc', [status(thm)], ['158', '159'])).
% 0.64/0.84  thf('161', plain, (~ (v2_struct_0 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('162', plain, ((v2_struct_0 @ sk_D_1)),
% 0.64/0.84      inference('clc', [status(thm)], ['160', '161'])).
% 0.64/0.84  thf('163', plain, ($false), inference('demod', [status(thm)], ['0', '162'])).
% 0.64/0.84  
% 0.64/0.84  % SZS output end Refutation
% 0.64/0.84  
% 0.64/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
