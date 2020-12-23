%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LTEQQam7Y3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:54 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 741 expanded)
%              Number of leaves         :   38 ( 224 expanded)
%              Depth                    :   22
%              Number of atoms          : 2123 (23121 expanded)
%              Number of equality atoms :   11 ( 336 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( m1_connsp_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
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

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X26 ) @ X27 )
      | ~ ( v1_tsep_1 @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X27 ) ) ),
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
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
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

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ X18 @ ( k1_connsp_2 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ),
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
    ( ( v2_struct_0 @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['26','32','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('45',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('73',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['66'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('75',plain,(
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

thf('76',plain,(
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
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['73','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['70'])).

thf('92',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['66'])).

thf('102',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['71','100','101'])).

thf('103',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['69','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('105',plain,(
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

thf('106',plain,(
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
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('117',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','119'])).

thf('121',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['52','53'])).

thf('122',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('123',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tarski @ ( sk_D @ X25 @ X23 @ X24 ) @ X25 )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['52','53'])).

thf('134',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('135',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_connsp_2 @ ( sk_D @ X25 @ X23 @ X24 ) @ X24 @ X23 )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','132','144'])).

thf('146',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['70'])).

thf('147',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['71','100'])).

thf('148',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['0','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LTEQQam7Y3
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 168 iterations in 0.128s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.63  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.42/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.42/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.63  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.42/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.42/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.63  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.42/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.42/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.63  thf(t67_tmap_1, conjecture,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.63             ( l1_pre_topc @ B ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.42/0.63                 ( m1_subset_1 @
% 0.42/0.63                   C @ 
% 0.42/0.63                   ( k1_zfmisc_1 @
% 0.42/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.42/0.63               ( ![D:$i]:
% 0.42/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.42/0.63                     ( m1_pre_topc @ D @ B ) ) =>
% 0.42/0.63                   ( ![E:$i]:
% 0.42/0.63                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.42/0.63                       ( ![F:$i]:
% 0.42/0.63                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.42/0.63                           ( ( ( E ) = ( F ) ) =>
% 0.42/0.63                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.42/0.63                               ( r1_tmap_1 @
% 0.42/0.63                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i]:
% 0.42/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.63            ( l1_pre_topc @ A ) ) =>
% 0.42/0.63          ( ![B:$i]:
% 0.42/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.63                ( l1_pre_topc @ B ) ) =>
% 0.42/0.63              ( ![C:$i]:
% 0.42/0.63                ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.63                    ( v1_funct_2 @
% 0.42/0.63                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.42/0.63                    ( m1_subset_1 @
% 0.42/0.63                      C @ 
% 0.42/0.63                      ( k1_zfmisc_1 @
% 0.42/0.63                        ( k2_zfmisc_1 @
% 0.42/0.63                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.42/0.63                  ( ![D:$i]:
% 0.42/0.63                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.42/0.63                        ( m1_pre_topc @ D @ B ) ) =>
% 0.42/0.63                      ( ![E:$i]:
% 0.42/0.63                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.42/0.63                          ( ![F:$i]:
% 0.42/0.63                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.42/0.63                              ( ( ( E ) = ( F ) ) =>
% 0.42/0.63                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.42/0.63                                  ( r1_tmap_1 @
% 0.42/0.63                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.42/0.63  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('2', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(t1_tsep_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.42/0.63           ( m1_subset_1 @
% 0.42/0.63             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.63  thf('3', plain,
% 0.42/0.63      (![X29 : $i, X30 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X29 @ X30)
% 0.42/0.63          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.42/0.63          | ~ (l1_pre_topc @ X30))),
% 0.42/0.63      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      ((~ (l1_pre_topc @ sk_B)
% 0.42/0.63        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.42/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.63  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('6', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf(t5_connsp_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.63               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.42/0.63                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.63          | ~ (v3_pre_topc @ X20 @ X21)
% 0.42/0.63          | ~ (r2_hidden @ X22 @ X20)
% 0.42/0.63          | (m1_connsp_2 @ X20 @ X21 @ X22)
% 0.42/0.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.42/0.63          | ~ (l1_pre_topc @ X21)
% 0.42/0.63          | ~ (v2_pre_topc @ X21)
% 0.42/0.63          | (v2_struct_0 @ X21))),
% 0.42/0.63      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.42/0.63  thf('8', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_B)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.63  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('11', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf(t16_tsep_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.42/0.63                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.42/0.63                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X26 @ X27)
% 0.42/0.63          | ((X28) != (u1_struct_0 @ X26))
% 0.42/0.63          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.42/0.63          | ~ (m1_pre_topc @ X26 @ X27)
% 0.42/0.63          | (v3_pre_topc @ X28 @ X27)
% 0.42/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.42/0.63          | ~ (l1_pre_topc @ X27)
% 0.42/0.63          | ~ (v2_pre_topc @ X27))),
% 0.42/0.63      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.42/0.63  thf('13', plain,
% 0.42/0.63      (![X26 : $i, X27 : $i]:
% 0.42/0.63         (~ (v2_pre_topc @ X27)
% 0.42/0.63          | ~ (l1_pre_topc @ X27)
% 0.42/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.42/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.42/0.63          | (v3_pre_topc @ (u1_struct_0 @ X26) @ X27)
% 0.42/0.63          | ~ (v1_tsep_1 @ X26 @ X27)
% 0.42/0.63          | ~ (m1_pre_topc @ X26 @ X27))),
% 0.42/0.63      inference('simplify', [status(thm)], ['12'])).
% 0.42/0.63  thf('14', plain,
% 0.42/0.63      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.42/0.63        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.42/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['11', '13'])).
% 0.42/0.63  thf('15', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('16', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('19', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.42/0.63      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.42/0.63  thf('20', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.42/0.63      inference('demod', [status(thm)], ['8', '9', '10', '19'])).
% 0.42/0.63  thf('21', plain,
% 0.42/0.63      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.42/0.63        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['1', '20'])).
% 0.42/0.63  thf('22', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('23', plain, (((sk_E) = (sk_F))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('24', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf(t30_connsp_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.63           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.42/0.63  thf('25', plain,
% 0.42/0.63      (![X18 : $i, X19 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.42/0.63          | (r2_hidden @ X18 @ (k1_connsp_2 @ X19 @ X18))
% 0.42/0.63          | ~ (l1_pre_topc @ X19)
% 0.42/0.63          | ~ (v2_pre_topc @ X19)
% 0.42/0.63          | (v2_struct_0 @ X19))),
% 0.42/0.63      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_D_1)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_D_1)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_D_1)
% 0.42/0.63        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.63  thf('27', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(cc1_pre_topc, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.42/0.63  thf('28', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X6 @ X7)
% 0.42/0.63          | (v2_pre_topc @ X6)
% 0.42/0.63          | ~ (l1_pre_topc @ X7)
% 0.42/0.63          | ~ (v2_pre_topc @ X7))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.42/0.63  thf('29', plain,
% 0.42/0.63      ((~ (v2_pre_topc @ sk_B)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63        | (v2_pre_topc @ sk_D_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.63  thf('30', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('32', plain, ((v2_pre_topc @ sk_D_1)),
% 0.42/0.63      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.42/0.63  thf('33', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(dt_m1_pre_topc, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.42/0.63  thf('34', plain,
% 0.42/0.63      (![X8 : $i, X9 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.42/0.63  thf('35', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.63  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('37', plain, ((l1_pre_topc @ sk_D_1)),
% 0.42/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.63  thf('38', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_D_1)
% 0.42/0.63        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.42/0.63      inference('demod', [status(thm)], ['26', '32', '37'])).
% 0.42/0.63  thf('39', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('40', plain, ((r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E))),
% 0.42/0.63      inference('clc', [status(thm)], ['38', '39'])).
% 0.42/0.63  thf('41', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf(dt_k1_connsp_2, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.63         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63       ( m1_subset_1 @
% 0.42/0.63         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.42/0.63  thf('42', plain,
% 0.42/0.63      (![X13 : $i, X14 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X13)
% 0.42/0.63          | ~ (v2_pre_topc @ X13)
% 0.42/0.63          | (v2_struct_0 @ X13)
% 0.42/0.63          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.42/0.63          | (m1_subset_1 @ (k1_connsp_2 @ X13 @ X14) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.42/0.63  thf('43', plain,
% 0.42/0.63      (((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.42/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.42/0.63        | (v2_struct_0 @ sk_D_1)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_D_1)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_D_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.63  thf('44', plain, ((v2_pre_topc @ sk_D_1)),
% 0.42/0.63      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.42/0.63  thf('45', plain, ((l1_pre_topc @ sk_D_1)),
% 0.42/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.63  thf('46', plain,
% 0.42/0.63      (((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.42/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.42/0.63        | (v2_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.42/0.63  thf('47', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      ((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.42/0.63      inference('clc', [status(thm)], ['46', '47'])).
% 0.42/0.63  thf(l3_subset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.63  thf('49', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.42/0.63          | (r2_hidden @ X0 @ X2)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.42/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.63  thf('50', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.42/0.63  thf('51', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['40', '50'])).
% 0.42/0.63  thf('52', plain,
% 0.42/0.63      (((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('demod', [status(thm)], ['21', '51'])).
% 0.42/0.63  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('54', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)),
% 0.42/0.63      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.63  thf('55', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf(t7_connsp_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.42/0.63                    ( ![D:$i]:
% 0.42/0.63                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.63                          ( m1_subset_1 @
% 0.42/0.63                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.42/0.63                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('56', plain,
% 0.42/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.42/0.63          | (m1_subset_1 @ (sk_D @ X25 @ X23 @ X24) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.42/0.63          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.42/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.42/0.63          | ~ (l1_pre_topc @ X24)
% 0.42/0.63          | ~ (v2_pre_topc @ X24)
% 0.42/0.63          | (v2_struct_0 @ X24))),
% 0.42/0.63      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.42/0.63  thf('57', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_B)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.63  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('60', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.42/0.63  thf('61', plain,
% 0.42/0.63      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.42/0.63        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['54', '60'])).
% 0.42/0.63  thf('62', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('63', plain,
% 0.42/0.63      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.42/0.63  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('65', plain,
% 0.42/0.63      ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('clc', [status(thm)], ['63', '64'])).
% 0.42/0.63  thf('66', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)
% 0.42/0.63        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('67', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.42/0.63      inference('split', [status(esa)], ['66'])).
% 0.42/0.63  thf('68', plain, (((sk_E) = (sk_F))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('69', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.42/0.63      inference('demod', [status(thm)], ['67', '68'])).
% 0.42/0.63  thf('70', plain,
% 0.42/0.63      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)
% 0.42/0.63        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('71', plain,
% 0.42/0.63      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.42/0.63       ~
% 0.42/0.63       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))),
% 0.42/0.63      inference('split', [status(esa)], ['70'])).
% 0.42/0.63  thf('72', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf('73', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('split', [status(esa)], ['66'])).
% 0.42/0.63  thf('74', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ 
% 0.42/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(t64_tmap_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.63             ( l1_pre_topc @ B ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.42/0.63                 ( m1_subset_1 @
% 0.42/0.63                   C @ 
% 0.42/0.63                   ( k1_zfmisc_1 @
% 0.42/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.42/0.63               ( ![D:$i]:
% 0.42/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.42/0.63                   ( ![E:$i]:
% 0.42/0.63                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.42/0.63                       ( ![F:$i]:
% 0.42/0.63                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.42/0.63                           ( ( ( ( E ) = ( F ) ) & 
% 0.42/0.63                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.42/0.63                             ( r1_tmap_1 @
% 0.42/0.63                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('75', plain,
% 0.42/0.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X31)
% 0.42/0.63          | ~ (v2_pre_topc @ X31)
% 0.42/0.63          | ~ (l1_pre_topc @ X31)
% 0.42/0.63          | (v2_struct_0 @ X32)
% 0.42/0.63          | ~ (m1_pre_topc @ X32 @ X31)
% 0.42/0.63          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.42/0.63          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.42/0.63          | ((X36) != (X33))
% 0.42/0.63          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 0.42/0.63          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.42/0.63          | ~ (m1_subset_1 @ X35 @ 
% 0.42/0.63               (k1_zfmisc_1 @ 
% 0.42/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.42/0.63          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.42/0.63          | ~ (v1_funct_1 @ X35)
% 0.42/0.63          | ~ (l1_pre_topc @ X34)
% 0.42/0.63          | ~ (v2_pre_topc @ X34)
% 0.42/0.63          | (v2_struct_0 @ X34))),
% 0.42/0.63      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.42/0.63  thf('76', plain,
% 0.42/0.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X34)
% 0.42/0.63          | ~ (v2_pre_topc @ X34)
% 0.42/0.63          | ~ (l1_pre_topc @ X34)
% 0.42/0.63          | ~ (v1_funct_1 @ X35)
% 0.42/0.63          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.42/0.63          | ~ (m1_subset_1 @ X35 @ 
% 0.42/0.63               (k1_zfmisc_1 @ 
% 0.42/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.42/0.63          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.42/0.63          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 0.42/0.63          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.42/0.63          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.42/0.63          | ~ (m1_pre_topc @ X32 @ X31)
% 0.42/0.63          | (v2_struct_0 @ X32)
% 0.42/0.63          | ~ (l1_pre_topc @ X31)
% 0.42/0.63          | ~ (v2_pre_topc @ X31)
% 0.42/0.63          | (v2_struct_0 @ X31))),
% 0.42/0.63      inference('simplify', [status(thm)], ['75'])).
% 0.42/0.63  thf('77', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_B)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.42/0.63          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.42/0.63          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.63          | ~ (v1_funct_1 @ sk_C)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.63          | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['74', '76'])).
% 0.42/0.63  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('80', plain,
% 0.42/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('84', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.42/0.63          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.42/0.63          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)],
% 0.42/0.63                ['77', '78', '79', '80', '81', '82', '83'])).
% 0.42/0.63  thf('85', plain,
% 0.42/0.63      ((![X0 : $i]:
% 0.42/0.63          ((v2_struct_0 @ sk_A)
% 0.42/0.63           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.42/0.63           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.42/0.63              sk_E)
% 0.42/0.63           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.42/0.63           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.42/0.63           | (v2_struct_0 @ X0)
% 0.42/0.63           | (v2_struct_0 @ sk_B)))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['73', '84'])).
% 0.42/0.63  thf('86', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('87', plain,
% 0.42/0.63      ((![X0 : $i]:
% 0.42/0.63          ((v2_struct_0 @ sk_A)
% 0.42/0.63           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.42/0.63              sk_E)
% 0.42/0.63           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.42/0.63           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.42/0.63           | (v2_struct_0 @ X0)
% 0.42/0.63           | (v2_struct_0 @ sk_B)))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('demod', [status(thm)], ['85', '86'])).
% 0.42/0.63  thf('88', plain,
% 0.42/0.63      ((((v2_struct_0 @ sk_B)
% 0.42/0.63         | (v2_struct_0 @ sk_D_1)
% 0.42/0.63         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.42/0.63         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)
% 0.42/0.63         | (v2_struct_0 @ sk_A)))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['72', '87'])).
% 0.42/0.63  thf('89', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('90', plain,
% 0.42/0.63      ((((v2_struct_0 @ sk_B)
% 0.42/0.63         | (v2_struct_0 @ sk_D_1)
% 0.42/0.63         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)
% 0.42/0.63         | (v2_struct_0 @ sk_A)))
% 0.42/0.63         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('demod', [status(thm)], ['88', '89'])).
% 0.42/0.63  thf('91', plain,
% 0.42/0.63      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))
% 0.42/0.63         <= (~
% 0.42/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.42/0.63      inference('split', [status(esa)], ['70'])).
% 0.42/0.63  thf('92', plain, (((sk_E) = (sk_F))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('93', plain,
% 0.42/0.63      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E))
% 0.42/0.63         <= (~
% 0.42/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.42/0.63      inference('demod', [status(thm)], ['91', '92'])).
% 0.42/0.63  thf('94', plain,
% 0.42/0.63      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.42/0.63         <= (~
% 0.42/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.42/0.63             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['90', '93'])).
% 0.42/0.63  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('96', plain,
% 0.42/0.63      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.42/0.63         <= (~
% 0.42/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.42/0.63             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('clc', [status(thm)], ['94', '95'])).
% 0.42/0.63  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('98', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_D_1))
% 0.42/0.63         <= (~
% 0.42/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.42/0.63             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('clc', [status(thm)], ['96', '97'])).
% 0.42/0.63  thf('99', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('100', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) | 
% 0.42/0.63       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.42/0.63      inference('sup-', [status(thm)], ['98', '99'])).
% 0.42/0.63  thf('101', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) | 
% 0.42/0.63       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.42/0.63      inference('split', [status(esa)], ['66'])).
% 0.42/0.63  thf('102', plain,
% 0.42/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))),
% 0.42/0.63      inference('sat_resolution*', [status(thm)], ['71', '100', '101'])).
% 0.42/0.63  thf('103', plain,
% 0.42/0.63      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.42/0.63        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)),
% 0.42/0.63      inference('simpl_trail', [status(thm)], ['69', '102'])).
% 0.42/0.63  thf('104', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_C @ 
% 0.42/0.63        (k1_zfmisc_1 @ 
% 0.42/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(t65_tmap_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.63             ( l1_pre_topc @ B ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.42/0.63                 ( m1_subset_1 @
% 0.42/0.63                   C @ 
% 0.42/0.63                   ( k1_zfmisc_1 @
% 0.42/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.42/0.63               ( ![D:$i]:
% 0.42/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.42/0.63                   ( ![E:$i]:
% 0.42/0.63                     ( ( m1_subset_1 @
% 0.42/0.63                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.42/0.63                       ( ![F:$i]:
% 0.42/0.63                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.42/0.63                           ( ![G:$i]:
% 0.42/0.63                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.42/0.63                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.42/0.63                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.42/0.63                                   ( ( F ) = ( G ) ) ) =>
% 0.42/0.63                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.42/0.63                                   ( r1_tmap_1 @
% 0.42/0.63                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('105', plain,
% 0.42/0.63      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X37)
% 0.42/0.63          | ~ (v2_pre_topc @ X37)
% 0.42/0.63          | ~ (l1_pre_topc @ X37)
% 0.42/0.63          | (v2_struct_0 @ X38)
% 0.42/0.63          | ~ (m1_pre_topc @ X38 @ X37)
% 0.42/0.63          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.42/0.63          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.42/0.63          | ~ (m1_connsp_2 @ X40 @ X37 @ X39)
% 0.42/0.63          | ((X39) != (X41))
% 0.42/0.63          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.42/0.63               X41)
% 0.42/0.63          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X39)
% 0.42/0.63          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.42/0.63          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.42/0.63          | ~ (m1_subset_1 @ X43 @ 
% 0.42/0.63               (k1_zfmisc_1 @ 
% 0.42/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.42/0.63          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.42/0.63          | ~ (v1_funct_1 @ X43)
% 0.42/0.63          | ~ (l1_pre_topc @ X42)
% 0.42/0.63          | ~ (v2_pre_topc @ X42)
% 0.42/0.63          | (v2_struct_0 @ X42))),
% 0.42/0.63      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.42/0.63  thf('106', plain,
% 0.42/0.63      (![X37 : $i, X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X42)
% 0.42/0.63          | ~ (v2_pre_topc @ X42)
% 0.42/0.63          | ~ (l1_pre_topc @ X42)
% 0.42/0.63          | ~ (v1_funct_1 @ X43)
% 0.42/0.63          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))
% 0.42/0.63          | ~ (m1_subset_1 @ X43 @ 
% 0.42/0.63               (k1_zfmisc_1 @ 
% 0.42/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X42))))
% 0.42/0.63          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.42/0.63          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.42/0.63          | (r1_tmap_1 @ X37 @ X42 @ X43 @ X41)
% 0.42/0.63          | ~ (r1_tmap_1 @ X38 @ X42 @ (k2_tmap_1 @ X37 @ X42 @ X43 @ X38) @ 
% 0.42/0.63               X41)
% 0.42/0.63          | ~ (m1_connsp_2 @ X40 @ X37 @ X41)
% 0.42/0.63          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X38))
% 0.42/0.63          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 0.42/0.63          | ~ (m1_pre_topc @ X38 @ X37)
% 0.42/0.63          | (v2_struct_0 @ X38)
% 0.42/0.63          | ~ (l1_pre_topc @ X37)
% 0.42/0.63          | ~ (v2_pre_topc @ X37)
% 0.42/0.63          | (v2_struct_0 @ X37))),
% 0.42/0.63      inference('simplify', [status(thm)], ['105'])).
% 0.42/0.63  thf('107', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_B)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.42/0.63          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.42/0.63          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.42/0.63               X1)
% 0.42/0.63          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.42/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.42/0.63          | ~ (v1_funct_1 @ sk_C)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.63          | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['104', '106'])).
% 0.42/0.63  thf('108', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('110', plain,
% 0.42/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('114', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.42/0.63          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.42/0.63          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.42/0.63               X1)
% 0.42/0.63          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.42/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63          | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)],
% 0.42/0.63                ['107', '108', '109', '110', '111', '112', '113'])).
% 0.42/0.63  thf('115', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_A)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.42/0.63          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.42/0.63          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.42/0.63          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.42/0.63          | (v2_struct_0 @ sk_D_1)
% 0.42/0.63          | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['103', '114'])).
% 0.42/0.63  thf('116', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.63  thf('117', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('118', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('119', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_A)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.42/0.63          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.42/0.63          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.42/0.63          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | (v2_struct_0 @ sk_D_1)
% 0.42/0.63          | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.42/0.63  thf('120', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_B)
% 0.42/0.63        | (v2_struct_0 @ sk_D_1)
% 0.42/0.63        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63             (u1_struct_0 @ sk_D_1))
% 0.42/0.63        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63             sk_B @ sk_E)
% 0.42/0.63        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.42/0.63        | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['65', '119'])).
% 0.42/0.63  thf('121', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)),
% 0.42/0.63      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.63  thf('122', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf('123', plain,
% 0.42/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.42/0.63          | (r1_tarski @ (sk_D @ X25 @ X23 @ X24) @ X25)
% 0.42/0.63          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.42/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.42/0.63          | ~ (l1_pre_topc @ X24)
% 0.42/0.63          | ~ (v2_pre_topc @ X24)
% 0.42/0.63          | (v2_struct_0 @ X24))),
% 0.42/0.63      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.42/0.63  thf('124', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_B)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.42/0.63             (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['122', '123'])).
% 0.42/0.63  thf('125', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('127', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.42/0.63             (u1_struct_0 @ sk_D_1))
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.42/0.63  thf('128', plain,
% 0.42/0.63      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.42/0.63        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63           (u1_struct_0 @ sk_D_1))
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['121', '127'])).
% 0.42/0.63  thf('129', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('130', plain,
% 0.42/0.63      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63         (u1_struct_0 @ sk_D_1))
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('demod', [status(thm)], ['128', '129'])).
% 0.42/0.63  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('132', plain,
% 0.42/0.63      ((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63        (u1_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('clc', [status(thm)], ['130', '131'])).
% 0.42/0.63  thf('133', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)),
% 0.42/0.63      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.63  thf('134', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.63  thf('135', plain,
% 0.42/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.42/0.63          | (m1_connsp_2 @ (sk_D @ X25 @ X23 @ X24) @ X24 @ X23)
% 0.42/0.63          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.42/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.42/0.63          | ~ (l1_pre_topc @ X24)
% 0.42/0.63          | ~ (v2_pre_topc @ X24)
% 0.42/0.63          | (v2_struct_0 @ X24))),
% 0.42/0.63      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.42/0.63  thf('136', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (v2_pre_topc @ sk_B)
% 0.42/0.63          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.63          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.42/0.63             sk_B @ X0)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['134', '135'])).
% 0.42/0.63  thf('137', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('138', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('139', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ sk_B)
% 0.42/0.63          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.42/0.63          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.42/0.63             sk_B @ X0)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.42/0.63  thf('140', plain,
% 0.42/0.63      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.42/0.63        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.42/0.63           sk_B @ sk_E)
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['133', '139'])).
% 0.42/0.63  thf('141', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('142', plain,
% 0.42/0.63      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B @ 
% 0.42/0.63         sk_E)
% 0.42/0.63        | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('demod', [status(thm)], ['140', '141'])).
% 0.42/0.63  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('144', plain,
% 0.42/0.63      ((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B @ 
% 0.42/0.63        sk_E)),
% 0.42/0.63      inference('clc', [status(thm)], ['142', '143'])).
% 0.42/0.63  thf('145', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_B)
% 0.42/0.63        | (v2_struct_0 @ sk_D_1)
% 0.42/0.63        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.42/0.63        | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['120', '132', '144'])).
% 0.42/0.63  thf('146', plain,
% 0.42/0.63      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.42/0.63         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.42/0.63      inference('split', [status(esa)], ['70'])).
% 0.42/0.63  thf('147', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.42/0.63      inference('sat_resolution*', [status(thm)], ['71', '100'])).
% 0.42/0.63  thf('148', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.42/0.63      inference('simpl_trail', [status(thm)], ['146', '147'])).
% 0.42/0.63  thf('149', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.42/0.63      inference('sup-', [status(thm)], ['145', '148'])).
% 0.42/0.63  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('151', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.42/0.63      inference('clc', [status(thm)], ['149', '150'])).
% 0.42/0.63  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('153', plain, ((v2_struct_0 @ sk_D_1)),
% 0.42/0.63      inference('clc', [status(thm)], ['151', '152'])).
% 0.42/0.63  thf('154', plain, ($false), inference('demod', [status(thm)], ['0', '153'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
