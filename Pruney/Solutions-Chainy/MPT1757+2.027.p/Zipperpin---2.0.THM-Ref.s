%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DxO8bQ4zdp

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 555 expanded)
%              Number of leaves         :   37 ( 169 expanded)
%              Depth                    :   28
%              Number of atoms          : 2130 (17715 expanded)
%              Number of equality atoms :   11 ( 253 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( m1_connsp_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( m1_connsp_2 @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 @ X15 )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r1_tarski @ ( sk_D @ X17 @ X15 @ X16 ) @ X17 )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
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
    inference(demod,[status(thm)],['1','2'])).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X24 @ X26 @ ( k2_tmap_1 @ X23 @ X26 @ X27 @ X24 ) @ X25 )
      | ( X28 != X25 )
      | ~ ( r1_tmap_1 @ X23 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ X23 @ X26 @ X27 @ X25 )
      | ( r1_tmap_1 @ X24 @ X26 @ ( k2_tmap_1 @ X23 @ X26 @ X27 @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_connsp_2 @ X32 @ X29 @ X31 )
      | ( X31 != X33 )
      | ~ ( r1_tmap_1 @ X30 @ X34 @ ( k2_tmap_1 @ X29 @ X34 @ X35 @ X30 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X34 @ X35 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('106',plain,(
    ! [X29: $i,X30: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X29 @ X34 @ X35 @ X33 )
      | ~ ( r1_tmap_1 @ X30 @ X34 @ ( k2_tmap_1 @ X29 @ X34 @ X35 @ X30 ) @ X33 )
      | ~ ( m1_connsp_2 @ X32 @ X29 @ X33 )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    inference(demod,[status(thm)],['1','2'])).

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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','119'])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['70'])).

thf('126',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['71','100'])).

thf('127',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('129',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('132',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('133',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['133','134'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('136',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('137',plain,(
    l1_struct_0 @ sk_D_1 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['130','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['0','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DxO8bQ4zdp
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 134 iterations in 0.068s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(t67_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.53                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.53                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.53                               ( r1_tmap_1 @
% 0.21/0.53                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53                ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                    ( v1_funct_2 @
% 0.21/0.53                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                    ( m1_subset_1 @
% 0.21/0.53                      C @ 
% 0.21/0.53                      ( k1_zfmisc_1 @
% 0.21/0.53                        ( k2_zfmisc_1 @
% 0.21/0.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.53                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                          ( ![F:$i]:
% 0.21/0.53                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.53                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.53                                  ( r1_tmap_1 @
% 0.21/0.53                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain, (((sk_E) = (sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t2_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ X1)
% 0.21/0.53          | (v1_xboole_0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t1_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( m1_subset_1 @
% 0.21/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.53          | ~ (l1_pre_topc @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t5_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.21/0.53                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.53          | ~ (v3_pre_topc @ X12 @ X13)
% 0.21/0.53          | ~ (r2_hidden @ X14 @ X12)
% 0.21/0.53          | (m1_connsp_2 @ X12 @ X13 @ X14)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.53          | ~ (l1_pre_topc @ X13)
% 0.21/0.53          | ~ (v2_pre_topc @ X13)
% 0.21/0.53          | (v2_struct_0 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t16_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.53                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.53          | ((X20) != (u1_struct_0 @ X18))
% 0.21/0.53          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.21/0.53          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.53          | (v3_pre_topc @ X20 @ X19)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.53          | ~ (l1_pre_topc @ X19)
% 0.21/0.53          | ~ (v2_pre_topc @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X19)
% 0.21/0.53          | ~ (l1_pre_topc @ X19)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.53          | (v3_pre_topc @ (u1_struct_0 @ X18) @ X19)
% 0.21/0.53          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.21/0.53          | ~ (m1_pre_topc @ X18 @ X19))),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.53        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.53        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf('21', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '26'])).
% 0.21/0.53  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.21/0.53        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t7_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.21/0.53                    ( ![D:$i]:
% 0.21/0.53                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.53                          ( m1_subset_1 @
% 0.21/0.53                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.21/0.53                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.53          | (m1_connsp_2 @ (sk_D @ X17 @ X15 @ X16) @ X16 @ X15)
% 0.21/0.53          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ~ (l1_pre_topc @ X16)
% 0.21/0.53          | ~ (v2_pre_topc @ X16)
% 0.21/0.53          | (v2_struct_0 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.21/0.53             sk_B @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.21/0.53             sk_B @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53           sk_B @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['30', '36'])).
% 0.21/0.53  thf('38', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53           sk_B @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B @ 
% 0.21/0.53         sk_E)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '29'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.53          | (r1_tarski @ (sk_D @ X17 @ X15 @ X16) @ X17)
% 0.21/0.53          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ~ (l1_pre_topc @ X16)
% 0.21/0.53          | ~ (v2_pre_topc @ X16)
% 0.21/0.53          | (v2_struct_0 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.21/0.53             (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.21/0.53             (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53           (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.53  thf('50', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53           (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53         (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '29'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X17 @ X15 @ X16) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ~ (l1_pre_topc @ X16)
% 0.21/0.53          | ~ (v2_pre_topc @ X16)
% 0.21/0.53          | (v2_struct_0 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['54', '60'])).
% 0.21/0.53  thf('62', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['66'])).
% 0.21/0.53  thf('68', plain, (((sk_E) = (sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.21/0.53       ~
% 0.21/0.53       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))),
% 0.21/0.53      inference('split', [status(esa)], ['70'])).
% 0.21/0.53  thf('72', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('split', [status(esa)], ['66'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t64_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.53                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.53                             ( r1_tmap_1 @
% 0.21/0.53                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X23)
% 0.21/0.53          | ~ (v2_pre_topc @ X23)
% 0.21/0.53          | ~ (l1_pre_topc @ X23)
% 0.21/0.53          | (v2_struct_0 @ X24)
% 0.21/0.53          | ~ (m1_pre_topc @ X24 @ X23)
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.21/0.53          | (r1_tmap_1 @ X24 @ X26 @ (k2_tmap_1 @ X23 @ X26 @ X27 @ X24) @ X25)
% 0.21/0.53          | ((X28) != (X25))
% 0.21/0.53          | ~ (r1_tmap_1 @ X23 @ X26 @ X27 @ X28)
% 0.21/0.53          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X23))
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))))
% 0.21/0.53          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ~ (l1_pre_topc @ X26)
% 0.21/0.53          | ~ (v2_pre_topc @ X26)
% 0.21/0.53          | (v2_struct_0 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X26)
% 0.21/0.53          | ~ (v2_pre_topc @ X26)
% 0.21/0.53          | ~ (l1_pre_topc @ X26)
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.21/0.53          | ~ (r1_tmap_1 @ X23 @ X26 @ X27 @ X25)
% 0.21/0.53          | (r1_tmap_1 @ X24 @ X26 @ (k2_tmap_1 @ X23 @ X26 @ X27 @ X24) @ X25)
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.21/0.53          | ~ (m1_pre_topc @ X24 @ X23)
% 0.21/0.53          | (v2_struct_0 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X23)
% 0.21/0.53          | ~ (v2_pre_topc @ X23)
% 0.21/0.53          | (v2_struct_0 @ X23))),
% 0.21/0.53      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['74', '76'])).
% 0.21/0.53  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['77', '78', '79', '80', '81', '82', '83'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_A)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53              sk_E)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['73', '84'])).
% 0.21/0.53  thf('86', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_A)
% 0.21/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53              sk_E)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_D_1)
% 0.21/0.53         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.53         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '87'])).
% 0.21/0.53  thf('89', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_D_1)
% 0.21/0.53         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['70'])).
% 0.21/0.53  thf('92', plain, (((sk_E) = (sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['90', '93'])).
% 0.21/0.53  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('clc', [status(thm)], ['94', '95'])).
% 0.21/0.53  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_D_1))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.53  thf('99', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('100', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) | 
% 0.21/0.53       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.53  thf('101', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) | 
% 0.21/0.53       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('split', [status(esa)], ['66'])).
% 0.21/0.53  thf('102', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['71', '100', '101'])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.53        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['69', '102'])).
% 0.21/0.53  thf('104', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t65_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @
% 0.21/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                           ( ![G:$i]:
% 0.21/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.53                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.21/0.53                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.53                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.53                                   ( r1_tmap_1 @
% 0.21/0.53                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('105', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X29)
% 0.21/0.53          | ~ (v2_pre_topc @ X29)
% 0.21/0.53          | ~ (l1_pre_topc @ X29)
% 0.21/0.53          | (v2_struct_0 @ X30)
% 0.21/0.53          | ~ (m1_pre_topc @ X30 @ X29)
% 0.21/0.53          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.21/0.53          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X30))
% 0.21/0.53          | ~ (m1_connsp_2 @ X32 @ X29 @ X31)
% 0.21/0.53          | ((X31) != (X33))
% 0.21/0.53          | ~ (r1_tmap_1 @ X30 @ X34 @ (k2_tmap_1 @ X29 @ X34 @ X35 @ X30) @ 
% 0.21/0.53               X33)
% 0.21/0.53          | (r1_tmap_1 @ X29 @ X34 @ X35 @ X31)
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X30))
% 0.21/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.53          | ~ (m1_subset_1 @ X35 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X34))))
% 0.21/0.53          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X34))
% 0.21/0.53          | ~ (v1_funct_1 @ X35)
% 0.21/0.53          | ~ (l1_pre_topc @ X34)
% 0.21/0.53          | ~ (v2_pre_topc @ X34)
% 0.21/0.53          | (v2_struct_0 @ X34))),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.21/0.53  thf('106', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X34)
% 0.21/0.53          | ~ (v2_pre_topc @ X34)
% 0.21/0.53          | ~ (l1_pre_topc @ X34)
% 0.21/0.53          | ~ (v1_funct_1 @ X35)
% 0.21/0.53          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X34))
% 0.21/0.53          | ~ (m1_subset_1 @ X35 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X34))))
% 0.21/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X30))
% 0.21/0.53          | (r1_tmap_1 @ X29 @ X34 @ X35 @ X33)
% 0.21/0.53          | ~ (r1_tmap_1 @ X30 @ X34 @ (k2_tmap_1 @ X29 @ X34 @ X35 @ X30) @ 
% 0.21/0.53               X33)
% 0.21/0.53          | ~ (m1_connsp_2 @ X32 @ X29 @ X33)
% 0.21/0.53          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X30))
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 0.21/0.53          | ~ (m1_pre_topc @ X30 @ X29)
% 0.21/0.53          | (v2_struct_0 @ X30)
% 0.21/0.53          | ~ (l1_pre_topc @ X29)
% 0.21/0.53          | ~ (v2_pre_topc @ X29)
% 0.21/0.53          | (v2_struct_0 @ X29))),
% 0.21/0.53      inference('simplify', [status(thm)], ['105'])).
% 0.21/0.53  thf('107', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53               X1)
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['104', '106'])).
% 0.21/0.53  thf('108', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('110', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('114', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53               X1)
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['107', '108', '109', '110', '111', '112', '113'])).
% 0.21/0.53  thf('115', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['103', '114'])).
% 0.21/0.53  thf('116', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('117', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('118', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('119', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.21/0.53  thf('120', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53             (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53             sk_B @ sk_E)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '119'])).
% 0.21/0.53  thf('121', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53             sk_B @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '120'])).
% 0.21/0.53  thf('122', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.21/0.53             sk_B @ sk_E)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['121'])).
% 0.21/0.53  thf('123', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '122'])).
% 0.21/0.53  thf('124', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['123'])).
% 0.21/0.53  thf('125', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.21/0.53      inference('split', [status(esa)], ['70'])).
% 0.21/0.53  thf('126', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['71', '100'])).
% 0.21/0.53  thf('127', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['125', '126'])).
% 0.21/0.53  thf('128', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['124', '127'])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('129', plain,
% 0.21/0.53      (![X5 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.21/0.53          | ~ (l1_struct_0 @ X5)
% 0.21/0.53          | (v2_struct_0 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('130', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['128', '129'])).
% 0.21/0.53  thf('131', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('132', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('133', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['131', '132'])).
% 0.21/0.53  thf('134', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('135', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['133', '134'])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('136', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('137', plain, ((l1_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['135', '136'])).
% 0.21/0.53  thf('138', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['130', '137'])).
% 0.21/0.53  thf('139', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('simplify', [status(thm)], ['138'])).
% 0.21/0.53  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('141', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['139', '140'])).
% 0.21/0.53  thf('142', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('143', plain, ((v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['141', '142'])).
% 0.21/0.53  thf('144', plain, ($false), inference('demod', [status(thm)], ['0', '143'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
