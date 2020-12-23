%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K2SCHTCQBD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:54 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  222 (1613 expanded)
%              Number of leaves         :   41 ( 470 expanded)
%              Depth                    :   24
%              Number of atoms          : 2649 (48282 expanded)
%              Number of equality atoms :   15 ( 717 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

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
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_connsp_2 @ ( sk_C @ X20 @ X19 ) @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
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
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
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
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','12','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['18','19'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('26',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

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

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( m1_subset_1 @ ( sk_D @ X26 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('34',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['1','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('53',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['46'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( r1_tmap_1 @ X33 @ X35 @ ( k2_tmap_1 @ X32 @ X35 @ X36 @ X33 ) @ X34 )
      | ( X37 != X34 )
      | ~ ( r1_tmap_1 @ X32 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_tmap_1 @ X32 @ X35 @ X36 @ X34 )
      | ( r1_tmap_1 @ X33 @ X35 @ ( k2_tmap_1 @ X32 @ X35 @ X36 @ X33 ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['50'])).

thf('72',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['46'])).

thf('82',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['51','80','81'])).

thf('83',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['49','82'])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v3_pre_topc @ X41 @ X38 )
      | ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( X40 != X42 )
      | ~ ( r1_tmap_1 @ X39 @ X43 @ ( k2_tmap_1 @ X38 @ X43 @ X44 @ X39 ) @ X42 )
      | ( r1_tmap_1 @ X38 @ X43 @ X44 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('86',plain,(
    ! [X38: $i,X39: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X39 ) )
      | ( r1_tmap_1 @ X38 @ X43 @ X44 @ X42 )
      | ~ ( r1_tmap_1 @ X39 @ X43 @ ( k2_tmap_1 @ X38 @ X43 @ X44 @ X39 ) @ X42 )
      | ~ ( r1_tarski @ X41 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r2_hidden @ X42 @ X41 )
      | ~ ( v3_pre_topc @ X41 @ X38 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
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
    inference(demod,[status(thm)],['87','88','89','90','91','92','93'])).

thf('95',plain,(
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
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_B )
    | ~ ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','99'])).

thf('101',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['18','19'])).

thf('102',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('103',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( m1_connsp_2 @ ( sk_D @ X26 @ X24 @ X25 ) @ X25 @ X24 )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('106',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('110',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

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

thf('114',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_connsp_2 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('117',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('121',plain,
    ( ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('125',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,(
    r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_B )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','123','126'])).

thf('128',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('129',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('130',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('131',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

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

thf('135',plain,(
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

thf('136',plain,(
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
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

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

thf('139',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( X29
       != ( u1_struct_0 @ X27 ) )
      | ~ ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('140',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['138','140'])).

thf('142',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['137','146','147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','149'])).

thf('151',plain,(
    r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['128','152'])).

thf('154',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['18','19'])).

thf('158',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('159',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( v3_pre_topc @ ( sk_D @ X26 @ X24 @ X25 ) @ X25 )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('162',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('166',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['153','154','156','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','169'])).

thf('171',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['50'])).

thf('172',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['51','80'])).

thf('173',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['0','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K2SCHTCQBD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 267 iterations in 0.143s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.60  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.60  thf(t67_tmap_1, conjecture,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.60                 ( m1_subset_1 @
% 0.38/0.60                   C @ 
% 0.38/0.60                   ( k1_zfmisc_1 @
% 0.38/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.38/0.60                     ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.60                   ( ![E:$i]:
% 0.38/0.60                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.60                       ( ![F:$i]:
% 0.38/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.60                           ( ( ( E ) = ( F ) ) =>
% 0.38/0.60                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.38/0.60                               ( r1_tmap_1 @
% 0.38/0.60                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]:
% 0.38/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.60            ( l1_pre_topc @ A ) ) =>
% 0.38/0.60          ( ![B:$i]:
% 0.38/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60                ( l1_pre_topc @ B ) ) =>
% 0.38/0.60              ( ![C:$i]:
% 0.38/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                    ( v1_funct_2 @
% 0.38/0.60                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.60                    ( m1_subset_1 @
% 0.38/0.60                      C @ 
% 0.38/0.60                      ( k1_zfmisc_1 @
% 0.38/0.60                        ( k2_zfmisc_1 @
% 0.38/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.60                  ( ![D:$i]:
% 0.38/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.38/0.60                        ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.60                      ( ![E:$i]:
% 0.38/0.60                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.60                          ( ![F:$i]:
% 0.38/0.60                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.60                              ( ( ( E ) = ( F ) ) =>
% 0.38/0.60                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.38/0.60                                  ( r1_tmap_1 @
% 0.38/0.60                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.38/0.60  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('2', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('3', plain, (((sk_E) = (sk_F))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf(existence_m1_connsp_2, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.60         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         (~ (l1_pre_topc @ X19)
% 0.38/0.60          | ~ (v2_pre_topc @ X19)
% 0.38/0.60          | (v2_struct_0 @ X19)
% 0.38/0.60          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.38/0.60          | (m1_connsp_2 @ (sk_C @ X20 @ X19) @ X19 @ X20))),
% 0.38/0.60      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.60  thf('7', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc1_pre_topc, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X6 : $i, X7 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X6 @ X7)
% 0.38/0.60          | (v2_pre_topc @ X6)
% 0.38/0.60          | ~ (l1_pre_topc @ X7)
% 0.38/0.60          | ~ (v2_pre_topc @ X7))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((~ (v2_pre_topc @ sk_B)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60        | (v2_pre_topc @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.60  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('12', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.60  thf('13', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_m1_pre_topc, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( l1_pre_topc @ A ) =>
% 0.38/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.60  thf('15', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.60  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('17', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['6', '12', '17'])).
% 0.38/0.60  thf('19', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('20', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('21', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('22', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf(dt_m1_connsp_2, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.60         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60       ( ![C:$i]:
% 0.38/0.60         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.38/0.60           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.60         (~ (l1_pre_topc @ X16)
% 0.38/0.60          | ~ (v2_pre_topc @ X16)
% 0.38/0.60          | (v2_struct_0 @ X16)
% 0.38/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.38/0.60          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.60          | ~ (m1_connsp_2 @ X18 @ X16 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.38/0.60          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | (v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf('25', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.60  thf('26', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.38/0.60          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.38/0.60  thf('28', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.38/0.60      inference('clc', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['21', '29'])).
% 0.38/0.60  thf(t7_connsp_2, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.38/0.60                    ( ![D:$i]:
% 0.38/0.60                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.38/0.60                          ( m1_subset_1 @
% 0.38/0.60                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.60                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.38/0.60                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.38/0.60          | (m1_subset_1 @ (sk_D @ X26 @ X24 @ X25) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.38/0.60          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.38/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.38/0.60          | ~ (l1_pre_topc @ X25)
% 0.38/0.60          | ~ (v2_pre_topc @ X25)
% 0.38/0.60          | (v2_struct_0 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.60  thf('34', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '35'])).
% 0.38/0.60  thf('37', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.60  thf('39', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.60  thf(t39_pre_topc, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( l1_pre_topc @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.60               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.60          | ~ (l1_pre_topc @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (l1_pre_topc @ X0)
% 0.38/0.60          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (m1_pre_topc @ sk_D_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60        | ~ (l1_pre_topc @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '42'])).
% 0.38/0.60  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.38/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.60      inference('split', [status(esa)], ['46'])).
% 0.38/0.60  thf('48', plain, (((sk_E) = (sk_F))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.38/0.60        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.38/0.60       ~
% 0.38/0.60       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.38/0.60      inference('split', [status(esa)], ['50'])).
% 0.38/0.60  thf('52', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('split', [status(esa)], ['46'])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t64_tmap_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.60                 ( m1_subset_1 @
% 0.38/0.60                   C @ 
% 0.38/0.60                   ( k1_zfmisc_1 @
% 0.38/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.60                   ( ![E:$i]:
% 0.38/0.60                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.60                       ( ![F:$i]:
% 0.38/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.60                           ( ( ( ( E ) = ( F ) ) & 
% 0.38/0.60                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.38/0.60                             ( r1_tmap_1 @
% 0.38/0.60                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X32)
% 0.38/0.60          | ~ (v2_pre_topc @ X32)
% 0.38/0.60          | ~ (l1_pre_topc @ X32)
% 0.38/0.60          | (v2_struct_0 @ X33)
% 0.38/0.60          | ~ (m1_pre_topc @ X33 @ X32)
% 0.38/0.60          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.38/0.60          | (r1_tmap_1 @ X33 @ X35 @ (k2_tmap_1 @ X32 @ X35 @ X36 @ X33) @ X34)
% 0.38/0.60          | ((X37) != (X34))
% 0.38/0.60          | ~ (r1_tmap_1 @ X32 @ X35 @ X36 @ X37)
% 0.38/0.60          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X32))
% 0.38/0.60          | ~ (m1_subset_1 @ X36 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))))
% 0.38/0.60          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))
% 0.38/0.60          | ~ (v1_funct_1 @ X36)
% 0.38/0.60          | ~ (l1_pre_topc @ X35)
% 0.38/0.60          | ~ (v2_pre_topc @ X35)
% 0.38/0.60          | (v2_struct_0 @ X35))),
% 0.38/0.60      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.38/0.60  thf('56', plain,
% 0.38/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X35)
% 0.38/0.60          | ~ (v2_pre_topc @ X35)
% 0.38/0.60          | ~ (l1_pre_topc @ X35)
% 0.38/0.60          | ~ (v1_funct_1 @ X36)
% 0.38/0.60          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))
% 0.38/0.60          | ~ (m1_subset_1 @ X36 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))))
% 0.38/0.60          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 0.38/0.60          | ~ (r1_tmap_1 @ X32 @ X35 @ X36 @ X34)
% 0.38/0.60          | (r1_tmap_1 @ X33 @ X35 @ (k2_tmap_1 @ X32 @ X35 @ X36 @ X33) @ X34)
% 0.38/0.60          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.38/0.60          | ~ (m1_pre_topc @ X33 @ X32)
% 0.38/0.60          | (v2_struct_0 @ X33)
% 0.38/0.60          | ~ (l1_pre_topc @ X32)
% 0.38/0.60          | ~ (v2_pre_topc @ X32)
% 0.38/0.60          | (v2_struct_0 @ X32))),
% 0.38/0.60      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.60  thf('57', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_B)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.60          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.38/0.60             X1)
% 0.38/0.60          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['54', '56'])).
% 0.38/0.60  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('60', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('64', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.60          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.38/0.60             X1)
% 0.38/0.60          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['57', '58', '59', '60', '61', '62', '63'])).
% 0.38/0.60  thf('65', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.60           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.60              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.38/0.60           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.38/0.60           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60           | (v2_struct_0 @ X0)
% 0.38/0.60           | (v2_struct_0 @ sk_B)))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['53', '64'])).
% 0.38/0.60  thf('66', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.60              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.38/0.60           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.38/0.60           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60           | (v2_struct_0 @ X0)
% 0.38/0.60           | (v2_struct_0 @ sk_B)))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.60  thf('68', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ sk_D_1)
% 0.38/0.60         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.60         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['52', '67'])).
% 0.38/0.60  thf('69', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ sk_D_1)
% 0.38/0.60         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('demod', [status(thm)], ['68', '69'])).
% 0.38/0.60  thf('71', plain,
% 0.38/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.38/0.60         <= (~
% 0.38/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.60      inference('split', [status(esa)], ['50'])).
% 0.38/0.60  thf('72', plain, (((sk_E) = (sk_F))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.38/0.60         <= (~
% 0.38/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf('74', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.38/0.60             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['70', '73'])).
% 0.38/0.60  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('76', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.38/0.60             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('clc', [status(thm)], ['74', '75'])).
% 0.38/0.60  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('78', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_D_1))
% 0.38/0.60         <= (~
% 0.38/0.60             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.38/0.60             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('clc', [status(thm)], ['76', '77'])).
% 0.38/0.60  thf('79', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('80', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.38/0.60       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('81', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.38/0.60       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.60      inference('split', [status(esa)], ['46'])).
% 0.38/0.60  thf('82', plain,
% 0.38/0.60      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['51', '80', '81'])).
% 0.38/0.60  thf('83', plain,
% 0.38/0.60      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.60        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['49', '82'])).
% 0.38/0.60  thf('84', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t66_tmap_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.60                 ( m1_subset_1 @
% 0.38/0.60                   C @ 
% 0.38/0.60                   ( k1_zfmisc_1 @
% 0.38/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.60                   ( ![E:$i]:
% 0.38/0.60                     ( ( m1_subset_1 @
% 0.38/0.60                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.60                       ( ![F:$i]:
% 0.38/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.60                           ( ![G:$i]:
% 0.38/0.60                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.60                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.38/0.60                                   ( r2_hidden @ F @ E ) & 
% 0.38/0.60                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.38/0.60                                   ( ( F ) = ( G ) ) ) =>
% 0.38/0.60                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.38/0.60                                   ( r1_tmap_1 @
% 0.38/0.60                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('85', plain,
% 0.38/0.60      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X38)
% 0.38/0.60          | ~ (v2_pre_topc @ X38)
% 0.38/0.60          | ~ (l1_pre_topc @ X38)
% 0.38/0.60          | (v2_struct_0 @ X39)
% 0.38/0.60          | ~ (m1_pre_topc @ X39 @ X38)
% 0.38/0.60          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X38))
% 0.38/0.60          | ~ (v3_pre_topc @ X41 @ X38)
% 0.38/0.60          | ~ (r2_hidden @ X40 @ X41)
% 0.38/0.60          | ~ (r1_tarski @ X41 @ (u1_struct_0 @ X39))
% 0.38/0.60          | ((X40) != (X42))
% 0.38/0.60          | ~ (r1_tmap_1 @ X39 @ X43 @ (k2_tmap_1 @ X38 @ X43 @ X44 @ X39) @ 
% 0.38/0.60               X42)
% 0.38/0.60          | (r1_tmap_1 @ X38 @ X43 @ X44 @ X40)
% 0.38/0.60          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X39))
% 0.38/0.60          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.38/0.60          | ~ (m1_subset_1 @ X44 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X43))))
% 0.38/0.60          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X43))
% 0.38/0.60          | ~ (v1_funct_1 @ X44)
% 0.38/0.60          | ~ (l1_pre_topc @ X43)
% 0.38/0.60          | ~ (v2_pre_topc @ X43)
% 0.38/0.60          | (v2_struct_0 @ X43))),
% 0.38/0.60      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.38/0.60  thf('86', plain,
% 0.38/0.60      (![X38 : $i, X39 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X43)
% 0.38/0.60          | ~ (v2_pre_topc @ X43)
% 0.38/0.60          | ~ (l1_pre_topc @ X43)
% 0.38/0.60          | ~ (v1_funct_1 @ X44)
% 0.38/0.60          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X43))
% 0.38/0.60          | ~ (m1_subset_1 @ X44 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X43))))
% 0.38/0.60          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.38/0.60          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X39))
% 0.38/0.60          | (r1_tmap_1 @ X38 @ X43 @ X44 @ X42)
% 0.38/0.60          | ~ (r1_tmap_1 @ X39 @ X43 @ (k2_tmap_1 @ X38 @ X43 @ X44 @ X39) @ 
% 0.38/0.60               X42)
% 0.38/0.60          | ~ (r1_tarski @ X41 @ (u1_struct_0 @ X39))
% 0.38/0.60          | ~ (r2_hidden @ X42 @ X41)
% 0.38/0.60          | ~ (v3_pre_topc @ X41 @ X38)
% 0.38/0.60          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X38))
% 0.38/0.60          | ~ (m1_pre_topc @ X39 @ X38)
% 0.38/0.60          | (v2_struct_0 @ X39)
% 0.38/0.60          | ~ (l1_pre_topc @ X38)
% 0.38/0.60          | ~ (v2_pre_topc @ X38)
% 0.38/0.60          | (v2_struct_0 @ X38))),
% 0.38/0.60      inference('simplify', [status(thm)], ['85'])).
% 0.38/0.60  thf('87', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_B)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ X2)
% 0.38/0.60          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.38/0.60          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['84', '86'])).
% 0.38/0.60  thf('88', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('90', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('91', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('94', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ X2)
% 0.38/0.60          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.60               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.38/0.60          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['87', '88', '89', '90', '91', '92', '93'])).
% 0.38/0.60  thf('95', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.60          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (r2_hidden @ sk_E @ X0)
% 0.38/0.60          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ sk_D_1)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['83', '94'])).
% 0.38/0.60  thf('96', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('97', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('98', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('99', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.60          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (r2_hidden @ sk_E @ X0)
% 0.38/0.60          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ sk_D_1)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.38/0.60  thf('100', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1)
% 0.38/0.60        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             sk_B)
% 0.38/0.60        | ~ (r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60        | ~ (r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '99'])).
% 0.38/0.60  thf('101', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('102', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['21', '29'])).
% 0.38/0.60  thf('103', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.38/0.60          | (m1_connsp_2 @ (sk_D @ X26 @ X24 @ X25) @ X25 @ X24)
% 0.38/0.60          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.38/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.38/0.60          | ~ (l1_pre_topc @ X25)
% 0.38/0.60          | ~ (v2_pre_topc @ X25)
% 0.38/0.60          | (v2_struct_0 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.38/0.60  thf('104', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             sk_D_1 @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['102', '103'])).
% 0.38/0.60  thf('105', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.60  thf('106', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('107', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             sk_D_1 @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.38/0.60  thf('108', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | (m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60           sk_D_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['101', '107'])).
% 0.38/0.60  thf('109', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('110', plain,
% 0.38/0.60      (((m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60         sk_D_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['108', '109'])).
% 0.38/0.60  thf('111', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('112', plain,
% 0.38/0.60      ((m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['110', '111'])).
% 0.38/0.60  thf('113', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.60  thf(t6_connsp_2, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.60               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.60  thf('114', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.60          | ~ (m1_connsp_2 @ X21 @ X22 @ X23)
% 0.38/0.60          | (r2_hidden @ X23 @ X21)
% 0.38/0.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.38/0.60          | ~ (l1_pre_topc @ X22)
% 0.38/0.60          | ~ (v2_pre_topc @ X22)
% 0.38/0.60          | (v2_struct_0 @ X22))),
% 0.38/0.60      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.38/0.60  thf('115', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60               sk_D_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['113', '114'])).
% 0.38/0.60  thf('116', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.60  thf('117', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('118', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60               sk_D_1 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.38/0.60  thf('119', plain,
% 0.38/0.60      (((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['112', '118'])).
% 0.38/0.60  thf('120', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('121', plain,
% 0.38/0.60      (((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['119', '120'])).
% 0.38/0.60  thf('122', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('123', plain,
% 0.38/0.60      ((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))),
% 0.38/0.60      inference('clc', [status(thm)], ['121', '122'])).
% 0.38/0.60  thf('124', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('125', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i]:
% 0.38/0.60         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('126', plain,
% 0.38/0.60      ((r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.60  thf('127', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1)
% 0.38/0.60        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             sk_B)
% 0.38/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['100', '123', '126'])).
% 0.38/0.60  thf('128', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.60  thf('129', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf('130', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t1_tsep_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( l1_pre_topc @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.60           ( m1_subset_1 @
% 0.38/0.60             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('131', plain,
% 0.38/0.60      (![X30 : $i, X31 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X30 @ X31)
% 0.38/0.60          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.38/0.60          | ~ (l1_pre_topc @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.60  thf('132', plain,
% 0.38/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.60        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['130', '131'])).
% 0.38/0.60  thf('133', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('134', plain,
% 0.38/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['132', '133'])).
% 0.38/0.60  thf(t9_tsep_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60                   ( ![E:$i]:
% 0.38/0.60                     ( ( m1_subset_1 @
% 0.38/0.60                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.60                       ( ( ( v3_pre_topc @ C @ A ) & 
% 0.38/0.60                           ( r1_tarski @ C @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                           ( r1_tarski @ D @ C ) & ( ( D ) = ( E ) ) ) =>
% 0.38/0.60                         ( ( v3_pre_topc @ E @ B ) <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('135', plain,
% 0.38/0.60      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X45 @ X46)
% 0.38/0.60          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.38/0.60          | ~ (v3_pre_topc @ X48 @ X46)
% 0.38/0.60          | ~ (r1_tarski @ X48 @ (u1_struct_0 @ X45))
% 0.38/0.60          | ~ (r1_tarski @ X47 @ X48)
% 0.38/0.60          | ((X47) != (X49))
% 0.38/0.60          | ~ (v3_pre_topc @ X49 @ X45)
% 0.38/0.60          | (v3_pre_topc @ X47 @ X46)
% 0.38/0.60          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.38/0.60          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.38/0.60          | ~ (l1_pre_topc @ X46)
% 0.38/0.60          | ~ (v2_pre_topc @ X46))),
% 0.38/0.60      inference('cnf', [status(esa)], [t9_tsep_1])).
% 0.38/0.60  thf('136', plain,
% 0.38/0.60      (![X45 : $i, X46 : $i, X48 : $i, X49 : $i]:
% 0.38/0.60         (~ (v2_pre_topc @ X46)
% 0.38/0.60          | ~ (l1_pre_topc @ X46)
% 0.38/0.60          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.38/0.60          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.38/0.60          | (v3_pre_topc @ X49 @ X46)
% 0.38/0.60          | ~ (v3_pre_topc @ X49 @ X45)
% 0.38/0.60          | ~ (r1_tarski @ X49 @ X48)
% 0.38/0.60          | ~ (r1_tarski @ X48 @ (u1_struct_0 @ X45))
% 0.38/0.60          | ~ (v3_pre_topc @ X48 @ X46)
% 0.38/0.60          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.38/0.60          | ~ (m1_pre_topc @ X45 @ X46))),
% 0.38/0.60      inference('simplify', [status(thm)], ['135'])).
% 0.38/0.60  thf('137', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.38/0.60          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (v3_pre_topc @ X1 @ X0)
% 0.38/0.60          | (v3_pre_topc @ X1 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['134', '136'])).
% 0.38/0.60  thf('138', plain,
% 0.38/0.60      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['132', '133'])).
% 0.38/0.60  thf(t16_tsep_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.60                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.38/0.60                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('139', plain,
% 0.38/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X27 @ X28)
% 0.38/0.60          | ((X29) != (u1_struct_0 @ X27))
% 0.38/0.60          | ~ (v1_tsep_1 @ X27 @ X28)
% 0.38/0.60          | ~ (m1_pre_topc @ X27 @ X28)
% 0.38/0.60          | (v3_pre_topc @ X29 @ X28)
% 0.38/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.38/0.60          | ~ (l1_pre_topc @ X28)
% 0.38/0.60          | ~ (v2_pre_topc @ X28))),
% 0.38/0.60      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.38/0.60  thf('140', plain,
% 0.38/0.60      (![X27 : $i, X28 : $i]:
% 0.38/0.60         (~ (v2_pre_topc @ X28)
% 0.38/0.60          | ~ (l1_pre_topc @ X28)
% 0.38/0.60          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.38/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.38/0.60          | (v3_pre_topc @ (u1_struct_0 @ X27) @ X28)
% 0.38/0.60          | ~ (v1_tsep_1 @ X27 @ X28)
% 0.38/0.60          | ~ (m1_pre_topc @ X27 @ X28))),
% 0.38/0.60      inference('simplify', [status(thm)], ['139'])).
% 0.38/0.60  thf('141', plain,
% 0.38/0.60      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.60        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.38/0.60        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['138', '140'])).
% 0.38/0.60  thf('142', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('143', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('144', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('145', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('146', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['141', '142', '143', '144', '145'])).
% 0.38/0.60  thf('147', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('148', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('149', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.60          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (v3_pre_topc @ X1 @ X0)
% 0.38/0.60          | (v3_pre_topc @ X1 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.60      inference('demod', [status(thm)], ['137', '146', '147', '148'])).
% 0.38/0.60  thf('150', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             sk_B)
% 0.38/0.60          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60               X0)
% 0.38/0.60          | ~ (r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60               (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['129', '149'])).
% 0.38/0.60  thf('151', plain,
% 0.38/0.60      ((r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.60  thf('152', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             sk_B)
% 0.38/0.60          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60               X0)
% 0.38/0.60          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['150', '151'])).
% 0.38/0.60  thf('153', plain,
% 0.38/0.60      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.60        | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60             sk_D_1)
% 0.38/0.60        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['128', '152'])).
% 0.38/0.60  thf('154', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(d10_xboole_0, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.60  thf('155', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.60  thf('156', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.60      inference('simplify', [status(thm)], ['155'])).
% 0.38/0.60  thf('157', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf('158', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['21', '29'])).
% 0.38/0.60  thf('159', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ X26 @ X24 @ X25) @ X25)
% 0.38/0.60          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.38/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.38/0.60          | ~ (l1_pre_topc @ X25)
% 0.38/0.60          | ~ (v2_pre_topc @ X25)
% 0.38/0.60          | (v2_struct_0 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.38/0.60  thf('160', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             sk_D_1)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['158', '159'])).
% 0.38/0.60  thf('161', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.60  thf('162', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('163', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             sk_D_1)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.38/0.60  thf('164', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60           sk_D_1)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['157', '163'])).
% 0.38/0.60  thf('165', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('166', plain,
% 0.38/0.60      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ sk_D_1)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['164', '165'])).
% 0.38/0.60  thf('167', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('168', plain,
% 0.38/0.60      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ sk_D_1)),
% 0.38/0.60      inference('clc', [status(thm)], ['166', '167'])).
% 0.38/0.60  thf('169', plain,
% 0.38/0.60      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['153', '154', '156', '168'])).
% 0.38/0.60  thf('170', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1)
% 0.38/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['127', '169'])).
% 0.38/0.60  thf('171', plain,
% 0.38/0.60      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.38/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('split', [status(esa)], ['50'])).
% 0.38/0.60  thf('172', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['51', '80'])).
% 0.38/0.60  thf('173', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['171', '172'])).
% 0.38/0.60  thf('174', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['170', '173'])).
% 0.38/0.60  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('176', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('clc', [status(thm)], ['174', '175'])).
% 0.38/0.60  thf('177', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('178', plain, ((v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('clc', [status(thm)], ['176', '177'])).
% 0.38/0.60  thf('179', plain, ($false), inference('demod', [status(thm)], ['0', '178'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
