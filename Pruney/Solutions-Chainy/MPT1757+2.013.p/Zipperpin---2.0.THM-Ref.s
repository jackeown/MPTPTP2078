%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hEuzM0yGL5

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  195 (1140 expanded)
%              Number of leaves         :   37 ( 336 expanded)
%              Depth                    :   22
%              Number of atoms          : 2128 (34553 expanded)
%              Number of equality atoms :   11 ( 512 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ( m1_connsp_2 @ ( sk_D @ X23 @ X21 @ X22 ) @ X22 @ X23 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( X27
       != ( u1_struct_0 @ X25 ) )
      | ~ ( v1_tsep_1 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v3_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X25 ) @ X26 )
      | ~ ( v1_tsep_1 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','19'])).

thf('21',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_connsp_2 @ ( sk_C @ X17 @ X16 ) @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('26',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('29',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['26','32','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['38','39'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_connsp_2 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('46',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

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

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('54',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_E @ ( sk_C @ sk_E @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('58',plain,
    ( ( r2_hidden @ sk_E @ ( sk_C @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ sk_E @ ( sk_C @ sk_E @ sk_D_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_E @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_connsp_2 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('84',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(split,[status(esa)],['77'])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X31 @ X33 @ ( k2_tmap_1 @ X30 @ X33 @ X34 @ X31 ) @ X32 )
      | ( X35 != X32 )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ X34 @ X32 )
      | ( r1_tmap_1 @ X31 @ X33 @ ( k2_tmap_1 @ X30 @ X33 @ X34 @ X31 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
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
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sup-',[status(thm)],['84','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['81'])).

thf('103',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(split,[status(esa)],['77'])).

thf('113',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['82','111','112'])).

thf('114',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['80','113'])).

thf('115',plain,(
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

thf('116',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tarski @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_connsp_2 @ X39 @ X36 @ X38 )
      | ( X38 != X40 )
      | ~ ( r1_tmap_1 @ X37 @ X41 @ ( k2_tmap_1 @ X36 @ X41 @ X42 @ X37 ) @ X40 )
      | ( r1_tmap_1 @ X36 @ X41 @ X42 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('117',plain,(
    ! [X36: $i,X37: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X37 ) )
      | ( r1_tmap_1 @ X36 @ X41 @ X42 @ X40 )
      | ~ ( r1_tmap_1 @ X37 @ X41 @ ( k2_tmap_1 @ X36 @ X41 @ X42 @ X37 ) @ X40 )
      | ~ ( m1_connsp_2 @ X39 @ X36 @ X40 )
      | ~ ( r1_tarski @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
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
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
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
    inference(demod,[status(thm)],['118','119','120','121','122','123','124'])).

thf('126',plain,(
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
    inference('sup-',[status(thm)],['114','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('134',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( sk_D @ X23 @ X21 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','140'])).

thf('142',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('143',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['65','66'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['131','145','146'])).

thf('148',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(split,[status(esa)],['81'])).

thf('149',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['82','111'])).

thf('150',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    $false ),
    inference(demod,[status(thm)],['0','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hEuzM0yGL5
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 190 iterations in 0.103s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(t67_tmap_1, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.56             ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.56                 ( m1_subset_1 @
% 0.20/0.56                   C @ 
% 0.20/0.56                   ( k1_zfmisc_1 @
% 0.20/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.20/0.56                     ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.56                   ( ![E:$i]:
% 0.20/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.56                       ( ![F:$i]:
% 0.20/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.56                           ( ( ( E ) = ( F ) ) =>
% 0.20/0.56                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.20/0.56                               ( r1_tmap_1 @
% 0.20/0.56                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56            ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.56                ( l1_pre_topc @ B ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.56                    ( v1_funct_2 @
% 0.20/0.56                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.56                    ( m1_subset_1 @
% 0.20/0.56                      C @ 
% 0.20/0.56                      ( k1_zfmisc_1 @
% 0.20/0.56                        ( k2_zfmisc_1 @
% 0.20/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.56                  ( ![D:$i]:
% 0.20/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.20/0.56                        ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.56                      ( ![E:$i]:
% 0.20/0.56                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.56                          ( ![F:$i]:
% 0.20/0.56                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.56                              ( ( ( E ) = ( F ) ) =>
% 0.20/0.56                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.20/0.56                                  ( r1_tmap_1 @
% 0.20/0.56                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.20/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('2', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t1_tsep_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( m1_subset_1 @
% 0.20/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X28 : $i, X29 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X28 @ X29)
% 0.20/0.56          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.56          | ~ (l1_pre_topc @ X29))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf(t9_connsp_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.56             ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.56                      ( ![D:$i]:
% 0.20/0.56                        ( ( m1_subset_1 @
% 0.20/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.20/0.56                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.56          | ~ (v3_pre_topc @ X21 @ X22)
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ X23 @ X21 @ X22) @ X22 @ X23)
% 0.20/0.56          | ~ (r2_hidden @ X23 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.56          | ~ (l1_pre_topc @ X22)
% 0.20/0.56          | ~ (v2_pre_topc @ X22)
% 0.20/0.56          | (v2_struct_0 @ X22))),
% 0.20/0.56      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             sk_B @ X0)
% 0.20/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf(t16_tsep_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.56                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.56                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.56          | ((X27) != (u1_struct_0 @ X25))
% 0.20/0.56          | ~ (v1_tsep_1 @ X25 @ X26)
% 0.20/0.56          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.56          | (v3_pre_topc @ X27 @ X26)
% 0.20/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.56          | ~ (l1_pre_topc @ X26)
% 0.20/0.56          | ~ (v2_pre_topc @ X26))),
% 0.20/0.56      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X26)
% 0.20/0.56          | ~ (l1_pre_topc @ X26)
% 0.20/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.56          | (v3_pre_topc @ (u1_struct_0 @ X25) @ X26)
% 0.20/0.56          | ~ (v1_tsep_1 @ X25 @ X26)
% 0.20/0.56          | ~ (m1_pre_topc @ X25 @ X26))),
% 0.20/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.56        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.20/0.56        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.56  thf('15', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('16', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('19', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.20/0.56      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             sk_B @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['8', '9', '10', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.20/0.56         sk_E)
% 0.20/0.56        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56        | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '20'])).
% 0.20/0.56  thf('22', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('23', plain, (((sk_E) = (sk_F))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf(existence_m1_connsp_2, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.20/0.56          | (m1_connsp_2 @ (sk_C @ X17 @ X16) @ X16 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.20/0.56        | (v2_struct_0 @ sk_D_1)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.56          | (v2_pre_topc @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X7)
% 0.20/0.56          | ~ (v2_pre_topc @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((~ (v2_pre_topc @ sk_B)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56        | (v2_pre_topc @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.56  thf('33', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_m1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.56  thf('35', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.56  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('37', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.20/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '32', '37'])).
% 0.20/0.56  thf('39', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('40', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.20/0.56      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.20/0.56      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('42', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf(dt_m1_connsp_2, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.20/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X13)
% 0.20/0.56          | ~ (v2_pre_topc @ X13)
% 0.20/0.56          | (v2_struct_0 @ X13)
% 0.20/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.56          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X15 @ X13 @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.56          | (v2_struct_0 @ sk_D_1)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.56  thf('46', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.56          | (v2_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.56  thf('48', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.20/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '49'])).
% 0.20/0.56  thf(t6_connsp_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X18 @ X19 @ X20)
% 0.20/0.56          | (r2_hidden @ X20 @ X18)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.20/0.56          | ~ (l1_pre_topc @ X19)
% 0.20/0.56          | ~ (v2_pre_topc @ X19)
% 0.20/0.56          | (v2_struct_0 @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_D_1)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.20/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.56  thf('53', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.56  thf('54', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_D_1)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1))
% 0.20/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))
% 0.20/0.56        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '55'])).
% 0.20/0.56  thf('57', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1)) | (v2_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('59', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('60', plain, ((r2_hidden @ sk_E @ (sk_C @ sk_E @ sk_D_1))),
% 0.20/0.56      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '49'])).
% 0.20/0.56  thf(l3_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.56          | (r2_hidden @ X0 @ X2)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (sk_C @ sk_E @ sk_D_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.56  thf('64', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.20/0.56         sk_E)
% 0.20/0.56        | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['21', '64'])).
% 0.20/0.56  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('67', plain,
% 0.20/0.56      ((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.20/0.56        sk_E)),
% 0.20/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf('68', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X13)
% 0.20/0.56          | ~ (v2_pre_topc @ X13)
% 0.20/0.56          | (v2_struct_0 @ X13)
% 0.20/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.56          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X15 @ X13 @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | (v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.56  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['67', '75'])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)
% 0.20/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.20/0.56      inference('split', [status(esa)], ['77'])).
% 0.20/0.56  thf('79', plain, (((sk_E) = (sk_F))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.20/0.56      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)
% 0.20/0.56        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)) | 
% 0.20/0.56       ~
% 0.20/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))),
% 0.20/0.56      inference('split', [status(esa)], ['81'])).
% 0.20/0.56  thf('83', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('84', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('split', [status(esa)], ['77'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_2 @ 
% 0.20/0.56        (k1_zfmisc_1 @ 
% 0.20/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t64_tmap_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.56             ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.56                 ( m1_subset_1 @
% 0.20/0.56                   C @ 
% 0.20/0.56                   ( k1_zfmisc_1 @
% 0.20/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.56                   ( ![E:$i]:
% 0.20/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.56                       ( ![F:$i]:
% 0.20/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.56                           ( ( ( ( E ) = ( F ) ) & 
% 0.20/0.56                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.20/0.56                             ( r1_tmap_1 @
% 0.20/0.56                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X30)
% 0.20/0.56          | ~ (v2_pre_topc @ X30)
% 0.20/0.56          | ~ (l1_pre_topc @ X30)
% 0.20/0.56          | (v2_struct_0 @ X31)
% 0.20/0.56          | ~ (m1_pre_topc @ X31 @ X30)
% 0.20/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.20/0.56          | (r1_tmap_1 @ X31 @ X33 @ (k2_tmap_1 @ X30 @ X33 @ X34 @ X31) @ X32)
% 0.20/0.56          | ((X35) != (X32))
% 0.20/0.56          | ~ (r1_tmap_1 @ X30 @ X33 @ X34 @ X35)
% 0.20/0.56          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X30))
% 0.20/0.56          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))))
% 0.20/0.56          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))
% 0.20/0.56          | ~ (v1_funct_1 @ X34)
% 0.20/0.56          | ~ (l1_pre_topc @ X33)
% 0.20/0.56          | ~ (v2_pre_topc @ X33)
% 0.20/0.56          | (v2_struct_0 @ X33))),
% 0.20/0.56      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.20/0.56  thf('87', plain,
% 0.20/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X33)
% 0.20/0.56          | ~ (v2_pre_topc @ X33)
% 0.20/0.56          | ~ (l1_pre_topc @ X33)
% 0.20/0.56          | ~ (v1_funct_1 @ X34)
% 0.20/0.56          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))
% 0.20/0.56          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))))
% 0.20/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.20/0.56          | ~ (r1_tmap_1 @ X30 @ X33 @ X34 @ X32)
% 0.20/0.56          | (r1_tmap_1 @ X31 @ X33 @ (k2_tmap_1 @ X30 @ X33 @ X34 @ X31) @ X32)
% 0.20/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.20/0.56          | ~ (m1_pre_topc @ X31 @ X30)
% 0.20/0.56          | (v2_struct_0 @ X31)
% 0.20/0.56          | ~ (l1_pre_topc @ X30)
% 0.20/0.56          | ~ (v2_pre_topc @ X30)
% 0.20/0.56          | (v2_struct_0 @ X30))),
% 0.20/0.56      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.56             X1)
% 0.20/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56               (u1_struct_0 @ sk_A))
% 0.20/0.56          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['85', '87'])).
% 0.20/0.56  thf('89', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('92', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('95', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ 
% 0.20/0.56             X1)
% 0.20/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)],
% 0.20/0.56                ['88', '89', '90', '91', '92', '93', '94'])).
% 0.20/0.56  thf('96', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.20/0.56           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.56              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ sk_E)
% 0.20/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.56           | (v2_struct_0 @ X0)
% 0.20/0.56           | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['84', '95'])).
% 0.20/0.56  thf('97', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('98', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.56              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ sk_E)
% 0.20/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.20/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.56           | (v2_struct_0 @ X0)
% 0.20/0.56           | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('demod', [status(thm)], ['96', '97'])).
% 0.20/0.56  thf('99', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_B)
% 0.20/0.56         | (v2_struct_0 @ sk_D_1)
% 0.20/0.56         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.56         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E)
% 0.20/0.56         | (v2_struct_0 @ sk_A)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['83', '98'])).
% 0.20/0.56  thf('100', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('101', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_B)
% 0.20/0.56         | (v2_struct_0 @ sk_D_1)
% 0.20/0.56         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E)
% 0.20/0.56         | (v2_struct_0 @ sk_A)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.56  thf('102', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.20/0.56      inference('split', [status(esa)], ['81'])).
% 0.20/0.56  thf('103', plain, (((sk_E) = (sk_F))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('104', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)))),
% 0.20/0.56      inference('demod', [status(thm)], ['102', '103'])).
% 0.20/0.56  thf('105', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['101', '104'])).
% 0.20/0.56  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('107', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.56  thf('108', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('109', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_D_1))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.56  thf('110', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('111', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) | 
% 0.20/0.56       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.20/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.56  thf('112', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F)) | 
% 0.20/0.56       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.20/0.56      inference('split', [status(esa)], ['77'])).
% 0.20/0.56  thf('113', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_F))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['82', '111', '112'])).
% 0.20/0.56  thf('114', plain,
% 0.20/0.56      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.20/0.56        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_D_1) @ sk_E)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['80', '113'])).
% 0.20/0.56  thf('115', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_2 @ 
% 0.20/0.56        (k1_zfmisc_1 @ 
% 0.20/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t65_tmap_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.56             ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.56                 ( m1_subset_1 @
% 0.20/0.56                   C @ 
% 0.20/0.56                   ( k1_zfmisc_1 @
% 0.20/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.56                   ( ![E:$i]:
% 0.20/0.56                     ( ( m1_subset_1 @
% 0.20/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.56                       ( ![F:$i]:
% 0.20/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.56                           ( ![G:$i]:
% 0.20/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.56                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.56                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.20/0.56                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.56                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.56                                   ( r1_tmap_1 @
% 0.20/0.56                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('116', plain,
% 0.20/0.56      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X36)
% 0.20/0.56          | ~ (v2_pre_topc @ X36)
% 0.20/0.56          | ~ (l1_pre_topc @ X36)
% 0.20/0.56          | (v2_struct_0 @ X37)
% 0.20/0.56          | ~ (m1_pre_topc @ X37 @ X36)
% 0.20/0.56          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.20/0.56          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X37))
% 0.20/0.56          | ~ (m1_connsp_2 @ X39 @ X36 @ X38)
% 0.20/0.56          | ((X38) != (X40))
% 0.20/0.56          | ~ (r1_tmap_1 @ X37 @ X41 @ (k2_tmap_1 @ X36 @ X41 @ X42 @ X37) @ 
% 0.20/0.56               X40)
% 0.20/0.56          | (r1_tmap_1 @ X36 @ X41 @ X42 @ X38)
% 0.20/0.56          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.20/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.20/0.56          | ~ (m1_subset_1 @ X42 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))))
% 0.20/0.56          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))
% 0.20/0.56          | ~ (v1_funct_1 @ X42)
% 0.20/0.56          | ~ (l1_pre_topc @ X41)
% 0.20/0.56          | ~ (v2_pre_topc @ X41)
% 0.20/0.56          | (v2_struct_0 @ X41))),
% 0.20/0.56      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.56  thf('117', plain,
% 0.20/0.56      (![X36 : $i, X37 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X41)
% 0.20/0.56          | ~ (v2_pre_topc @ X41)
% 0.20/0.56          | ~ (l1_pre_topc @ X41)
% 0.20/0.56          | ~ (v1_funct_1 @ X42)
% 0.20/0.56          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))
% 0.20/0.56          | ~ (m1_subset_1 @ X42 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))))
% 0.20/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.20/0.56          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.20/0.56          | (r1_tmap_1 @ X36 @ X41 @ X42 @ X40)
% 0.20/0.56          | ~ (r1_tmap_1 @ X37 @ X41 @ (k2_tmap_1 @ X36 @ X41 @ X42 @ X37) @ 
% 0.20/0.56               X40)
% 0.20/0.56          | ~ (m1_connsp_2 @ X39 @ X36 @ X40)
% 0.20/0.56          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X37))
% 0.20/0.56          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X36))
% 0.20/0.56          | ~ (m1_pre_topc @ X37 @ X36)
% 0.20/0.56          | (v2_struct_0 @ X37)
% 0.20/0.56          | ~ (l1_pre_topc @ X36)
% 0.20/0.56          | ~ (v2_pre_topc @ X36)
% 0.20/0.56          | (v2_struct_0 @ X36))),
% 0.20/0.56      inference('simplify', [status(thm)], ['116'])).
% 0.20/0.56  thf('118', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ X1)
% 0.20/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56               (u1_struct_0 @ sk_A))
% 0.20/0.56          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['115', '117'])).
% 0.20/0.56  thf('119', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('120', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('121', plain,
% 0.20/0.56      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('122', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('125', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.20/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X0) @ X1)
% 0.20/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)],
% 0.20/0.56                ['118', '119', '120', '121', '122', '123', '124'])).
% 0.20/0.56  thf('126', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ sk_D_1)
% 0.20/0.56          | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['114', '125'])).
% 0.20/0.56  thf('127', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('128', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('129', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('130', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (v2_struct_0 @ sk_D_1)
% 0.20/0.56          | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.20/0.56  thf('131', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_D_1)
% 0.20/0.56        | ~ (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             (u1_struct_0 @ sk_D_1))
% 0.20/0.56        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             sk_B @ sk_E)
% 0.20/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['76', '130'])).
% 0.20/0.56  thf('132', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('133', plain,
% 0.20/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('134', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.56          | ~ (v3_pre_topc @ X21 @ X22)
% 0.20/0.56          | (r1_tarski @ (sk_D @ X23 @ X21 @ X22) @ X21)
% 0.20/0.56          | ~ (r2_hidden @ X23 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.56          | ~ (l1_pre_topc @ X22)
% 0.20/0.56          | ~ (v2_pre_topc @ X22)
% 0.20/0.56          | (v2_struct_0 @ X22))),
% 0.20/0.56      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.56  thf('135', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['133', '134'])).
% 0.20/0.56  thf('136', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('138', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.20/0.56  thf('139', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.20/0.56      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.56  thf('140', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56             (u1_struct_0 @ sk_D_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['138', '139'])).
% 0.20/0.56  thf('141', plain,
% 0.20/0.56      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56         (u1_struct_0 @ sk_D_1))
% 0.20/0.56        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.20/0.56        | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['132', '140'])).
% 0.20/0.56  thf('142', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.56  thf('143', plain,
% 0.20/0.56      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56         (u1_struct_0 @ sk_D_1))
% 0.20/0.56        | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['141', '142'])).
% 0.20/0.56  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('145', plain,
% 0.20/0.56      ((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.20/0.56        (u1_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('clc', [status(thm)], ['143', '144'])).
% 0.20/0.56  thf('146', plain,
% 0.20/0.56      ((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.20/0.56        sk_E)),
% 0.20/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf('147', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_D_1)
% 0.20/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['131', '145', '146'])).
% 0.20/0.56  thf('148', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))
% 0.20/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)))),
% 0.20/0.56      inference('split', [status(esa)], ['81'])).
% 0.20/0.56  thf('149', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['82', '111'])).
% 0.20/0.56  thf('150', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_2 @ sk_E)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 0.20/0.56  thf('151', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['147', '150'])).
% 0.20/0.56  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('153', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.20/0.56      inference('clc', [status(thm)], ['151', '152'])).
% 0.20/0.56  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('155', plain, ((v2_struct_0 @ sk_D_1)),
% 0.20/0.56      inference('clc', [status(thm)], ['153', '154'])).
% 0.20/0.56  thf('156', plain, ($false), inference('demod', [status(thm)], ['0', '155'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
