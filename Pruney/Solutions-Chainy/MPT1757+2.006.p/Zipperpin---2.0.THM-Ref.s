%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GU7zQDAcEs

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 612 expanded)
%              Number of leaves         :   39 ( 187 expanded)
%              Depth                    :   25
%              Number of atoms          : 2002 (18908 expanded)
%              Number of equality atoms :   13 ( 281 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( m1_connsp_2 @ ( sk_C @ X19 @ X18 ) @ X18 @ X19 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_connsp_2 @ X17 @ X15 @ X16 ) ) ),
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

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( sk_D @ X22 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
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
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('37',plain,
    ( ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['48'])).

thf('56',plain,(
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

thf('57',plain,(
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

thf('58',plain,(
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
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('74',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['48'])).

thf('84',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['53','82','83'])).

thf('85',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['51','84'])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( v3_pre_topc @ X38 @ X35 )
      | ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X36 ) )
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
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('88',plain,(
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
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r2_hidden @ X39 @ X38 )
      | ~ ( v3_pre_topc @ X38 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
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
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
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
    inference(demod,[status(thm)],['89','90','91','92','93','94','95'])).

thf('97',plain,(
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
    inference('sup-',[status(thm)],['85','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('99',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','101'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('104',plain,(
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

thf('105',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X24 ) @ X25 )
      | ~ ( v1_tsep_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','111','113'])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','114'])).

thf('116',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['52'])).

thf('117',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['53','82'])).

thf('118',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['17','18'])).

thf('121',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('122',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('125',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('132',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['119','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GU7zQDAcEs
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 189 iterations in 0.112s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(t67_tmap_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56             ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.56                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                   ( ![E:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                       ( ![F:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.56                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.56                               ( r1_tmap_1 @
% 0.21/0.56                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.56            ( l1_pre_topc @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56                ( l1_pre_topc @ B ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                    ( v1_funct_2 @
% 0.21/0.56                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                    ( m1_subset_1 @
% 0.21/0.56                      C @ 
% 0.21/0.56                      ( k1_zfmisc_1 @
% 0.21/0.56                        ( k2_zfmisc_1 @
% 0.21/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56                  ( ![D:$i]:
% 0.21/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.56                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                      ( ![E:$i]:
% 0.21/0.56                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                          ( ![F:$i]:
% 0.21/0.56                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.56                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.56                                  ( r1_tmap_1 @
% 0.21/0.56                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('2', plain, (((sk_E) = (sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(existence_m1_connsp_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X18)
% 0.21/0.56          | ~ (v2_pre_topc @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.56          | (m1_connsp_2 @ (sk_C @ X19 @ X18) @ X18 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.21/0.56        | (v2_struct_0 @ sk_D_1)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_D_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.56  thf('6', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.56          | (v2_pre_topc @ X8)
% 0.21/0.56          | ~ (l1_pre_topc @ X9)
% 0.21/0.56          | ~ (v2_pre_topc @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      ((~ (v2_pre_topc @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | (v2_pre_topc @ sk_D_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.56  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_m1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.56          | (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (l1_pre_topc @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.56  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.21/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.21/0.56  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('19', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.21/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.21/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('21', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(dt_m1_connsp_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.21/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15)
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.56          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (m1_connsp_2 @ X17 @ X15 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.21/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56          | (v2_struct_0 @ sk_D_1)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_D_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.56  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.21/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56          | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.56  thf('27', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.21/0.56      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '28'])).
% 0.21/0.56  thf(t8_connsp_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.56                 ( ?[D:$i]:
% 0.21/0.56                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.56                     ( v3_pre_topc @ D @ A ) & 
% 0.21/0.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.56          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.21/0.56          | (r2_hidden @ X20 @ (sk_D @ X22 @ X20 @ X21))
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56          | ~ (l1_pre_topc @ X21)
% 0.21/0.56          | ~ (v2_pre_topc @ X21)
% 0.21/0.56          | (v2_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_D_1)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_D_1)
% 0.21/0.56          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1))
% 0.21/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.56  thf('33', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_D_1)
% 0.21/0.56          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1))
% 0.21/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | (r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.21/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '34'])).
% 0.21/0.56  thf('36', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.21/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))),
% 0.21/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.56  thf('40', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(t2_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r2_hidden @ X3 @ X4)
% 0.21/0.56          | (v1_xboole_0 @ X4)
% 0.21/0.56          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.56  thf('43', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t1_tsep_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.56           ( m1_subset_1 @
% 0.21/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.56          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.56          | ~ (l1_pre_topc @ X28))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.56      inference('split', [status(esa)], ['48'])).
% 0.21/0.56  thf('50', plain, (((sk_E) = (sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.21/0.56        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.21/0.56       ~
% 0.21/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.21/0.56      inference('split', [status(esa)], ['52'])).
% 0.21/0.56  thf('54', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('split', [status(esa)], ['48'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t64_tmap_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56             ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                   ( ![E:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                       ( ![F:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.56                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.56                             ( r1_tmap_1 @
% 0.21/0.56                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X29)
% 0.21/0.56          | ~ (v2_pre_topc @ X29)
% 0.21/0.56          | ~ (l1_pre_topc @ X29)
% 0.21/0.56          | (v2_struct_0 @ X30)
% 0.21/0.56          | ~ (m1_pre_topc @ X30 @ X29)
% 0.21/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.21/0.56          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.21/0.56          | ((X34) != (X31))
% 0.21/0.56          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X34)
% 0.21/0.56          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 0.21/0.56          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.21/0.56          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.21/0.56          | ~ (v1_funct_1 @ X33)
% 0.21/0.56          | ~ (l1_pre_topc @ X32)
% 0.21/0.56          | ~ (v2_pre_topc @ X32)
% 0.21/0.56          | (v2_struct_0 @ X32))),
% 0.21/0.56      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X32)
% 0.21/0.56          | ~ (v2_pre_topc @ X32)
% 0.21/0.56          | ~ (l1_pre_topc @ X32)
% 0.21/0.56          | ~ (v1_funct_1 @ X33)
% 0.21/0.56          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.21/0.56          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.21/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.21/0.56          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X31)
% 0.21/0.56          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.21/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.21/0.56          | ~ (m1_pre_topc @ X30 @ X29)
% 0.21/0.56          | (v2_struct_0 @ X30)
% 0.21/0.56          | ~ (l1_pre_topc @ X29)
% 0.21/0.56          | ~ (v2_pre_topc @ X29)
% 0.21/0.56          | (v2_struct_0 @ X29))),
% 0.21/0.56      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.21/0.56             X1)
% 0.21/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.56               (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['56', '58'])).
% 0.21/0.56  thf('60', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.21/0.56             X1)
% 0.21/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['59', '60', '61', '62', '63', '64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((v2_struct_0 @ sk_A)
% 0.21/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.56           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.56              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.21/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56           | (v2_struct_0 @ X0)
% 0.21/0.56           | (v2_struct_0 @ sk_B)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['55', '66'])).
% 0.21/0.56  thf('68', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((v2_struct_0 @ sk_A)
% 0.21/0.56           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.56              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.21/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56           | (v2_struct_0 @ X0)
% 0.21/0.56           | (v2_struct_0 @ sk_B)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_B)
% 0.21/0.56         | (v2_struct_0 @ sk_D_1)
% 0.21/0.56         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.56         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.21/0.56         | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['54', '69'])).
% 0.21/0.56  thf('71', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_B)
% 0.21/0.56         | (v2_struct_0 @ sk_D_1)
% 0.21/0.56         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.21/0.56         | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.56      inference('split', [status(esa)], ['52'])).
% 0.21/0.56  thf('74', plain, (((sk_E) = (sk_F))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['72', '75'])).
% 0.21/0.56  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_D_1))
% 0.21/0.56         <= (~
% 0.21/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.56  thf('81', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.21/0.56       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.21/0.56       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.56      inference('split', [status(esa)], ['48'])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['53', '82', '83'])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.56        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['51', '84'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t66_tmap_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.56             ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.56                   ( ![E:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @
% 0.21/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                       ( ![F:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                           ( ![G:$i]:
% 0.21/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.56                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.56                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.56                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.56                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.56                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.56                                   ( r1_tmap_1 @
% 0.21/0.56                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X35)
% 0.21/0.56          | ~ (v2_pre_topc @ X35)
% 0.21/0.56          | ~ (l1_pre_topc @ X35)
% 0.21/0.56          | (v2_struct_0 @ X36)
% 0.21/0.56          | ~ (m1_pre_topc @ X36 @ X35)
% 0.21/0.56          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.21/0.56          | ~ (v3_pre_topc @ X38 @ X35)
% 0.21/0.56          | ~ (r2_hidden @ X37 @ X38)
% 0.21/0.56          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X36))
% 0.21/0.56          | ((X37) != (X39))
% 0.21/0.56          | ~ (r1_tmap_1 @ X36 @ X40 @ (k2_tmap_1 @ X35 @ X40 @ X41 @ X36) @ 
% 0.21/0.56               X39)
% 0.21/0.56          | (r1_tmap_1 @ X35 @ X40 @ X41 @ X37)
% 0.21/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.21/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.21/0.56          | ~ (m1_subset_1 @ X41 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))))
% 0.21/0.56          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))
% 0.21/0.56          | ~ (v1_funct_1 @ X41)
% 0.21/0.56          | ~ (l1_pre_topc @ X40)
% 0.21/0.56          | ~ (v2_pre_topc @ X40)
% 0.21/0.56          | (v2_struct_0 @ X40))),
% 0.21/0.56      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      (![X35 : $i, X36 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X40)
% 0.21/0.56          | ~ (v2_pre_topc @ X40)
% 0.21/0.56          | ~ (l1_pre_topc @ X40)
% 0.21/0.56          | ~ (v1_funct_1 @ X41)
% 0.21/0.56          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))
% 0.21/0.56          | ~ (m1_subset_1 @ X41 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))))
% 0.21/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.21/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.21/0.56          | (r1_tmap_1 @ X35 @ X40 @ X41 @ X39)
% 0.21/0.56          | ~ (r1_tmap_1 @ X36 @ X40 @ (k2_tmap_1 @ X35 @ X40 @ X41 @ X36) @ 
% 0.21/0.56               X39)
% 0.21/0.56          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X36))
% 0.21/0.56          | ~ (r2_hidden @ X39 @ X38)
% 0.21/0.56          | ~ (v3_pre_topc @ X38 @ X35)
% 0.21/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X35))
% 0.21/0.56          | ~ (m1_pre_topc @ X36 @ X35)
% 0.21/0.56          | (v2_struct_0 @ X36)
% 0.21/0.56          | ~ (l1_pre_topc @ X35)
% 0.21/0.56          | ~ (v2_pre_topc @ X35)
% 0.21/0.56          | (v2_struct_0 @ X35))),
% 0.21/0.56      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.56  thf('89', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.56          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.56               (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['86', '88'])).
% 0.21/0.56  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('93', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.21/0.56          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['89', '90', '91', '92', '93', '94', '95'])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.56          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.56          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ sk_D_1)
% 0.21/0.56          | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['85', '96'])).
% 0.21/0.56  thf('98', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('99', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('100', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('101', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56          | ~ (r2_hidden @ sk_E @ X0)
% 0.21/0.56          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ sk_D_1)
% 0.21/0.56          | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.21/0.56  thf('102', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_D_1)
% 0.21/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.21/0.56        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['47', '101'])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf(t16_tsep_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.56                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('104', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.56         (~ (m1_pre_topc @ X24 @ X25)
% 0.21/0.56          | ((X26) != (u1_struct_0 @ X24))
% 0.21/0.56          | ~ (v1_tsep_1 @ X24 @ X25)
% 0.21/0.56          | ~ (m1_pre_topc @ X24 @ X25)
% 0.21/0.56          | (v3_pre_topc @ X26 @ X25)
% 0.21/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.56          | ~ (l1_pre_topc @ X25)
% 0.21/0.56          | ~ (v2_pre_topc @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i]:
% 0.21/0.56         (~ (v2_pre_topc @ X25)
% 0.21/0.56          | ~ (l1_pre_topc @ X25)
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.56          | (v3_pre_topc @ (u1_struct_0 @ X24) @ X25)
% 0.21/0.56          | ~ (v1_tsep_1 @ X24 @ X25)
% 0.21/0.56          | ~ (m1_pre_topc @ X24 @ X25))),
% 0.21/0.56      inference('simplify', [status(thm)], ['104'])).
% 0.21/0.56  thf('106', plain,
% 0.21/0.56      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.56        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.56        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['103', '105'])).
% 0.21/0.56  thf('107', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('108', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('110', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('111', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('112', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('113', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.56      inference('simplify', [status(thm)], ['112'])).
% 0.21/0.56  thf('114', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_D_1)
% 0.21/0.56        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['102', '111', '113'])).
% 0.21/0.56  thf('115', plain,
% 0.21/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.56        | (v2_struct_0 @ sk_D_1)
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['42', '114'])).
% 0.21/0.56  thf('116', plain,
% 0.21/0.56      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.21/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.56      inference('split', [status(esa)], ['52'])).
% 0.21/0.56  thf('117', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['53', '82'])).
% 0.21/0.56  thf('118', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 0.21/0.56  thf('119', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_D_1)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['115', '118'])).
% 0.21/0.56  thf('120', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.21/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('121', plain,
% 0.21/0.56      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '28'])).
% 0.21/0.56  thf('122', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.56          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ X22 @ X20 @ X21) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56          | ~ (l1_pre_topc @ X21)
% 0.21/0.56          | ~ (v2_pre_topc @ X21)
% 0.21/0.56          | (v2_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.21/0.56  thf('123', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_D_1)
% 0.21/0.56          | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_D_1)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.56  thf('124', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.56  thf('125', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('126', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_D_1)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.21/0.56  thf('127', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56        | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['120', '126'])).
% 0.21/0.56  thf('128', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('129', plain,
% 0.21/0.56      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.21/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['127', '128'])).
% 0.21/0.56  thf('130', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('131', plain,
% 0.21/0.56      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.56      inference('clc', [status(thm)], ['129', '130'])).
% 0.21/0.56  thf(t5_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.56  thf('132', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.56          | ~ (v1_xboole_0 @ X7)
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.56  thf('133', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['131', '132'])).
% 0.21/0.56  thf('134', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_D_1)
% 0.21/0.56          | (v2_struct_0 @ sk_B)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['119', '133'])).
% 0.21/0.56  thf('135', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['39', '134'])).
% 0.21/0.56  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('137', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1))),
% 0.21/0.56      inference('clc', [status(thm)], ['135', '136'])).
% 0.21/0.56  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('139', plain, ((v2_struct_0 @ sk_D_1)),
% 0.21/0.56      inference('clc', [status(thm)], ['137', '138'])).
% 0.21/0.56  thf('140', plain, ($false), inference('demod', [status(thm)], ['0', '139'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
