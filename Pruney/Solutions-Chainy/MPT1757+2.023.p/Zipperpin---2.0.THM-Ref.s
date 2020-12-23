%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bFkJE5pjLH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:57 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 390 expanded)
%              Number of leaves         :   36 ( 126 expanded)
%              Depth                    :   23
%              Number of atoms          : 2126 (12343 expanded)
%              Number of equality atoms :   11 ( 177 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ( m1_connsp_2 @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 @ X15 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
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
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','25'])).

thf('27',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ( r1_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X31 @ X28 @ X30 )
      | ( X30 != X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X33 @ X34 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('63',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X28 @ X33 @ X34 @ X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ~ ( m1_connsp_2 @ X31 @ X28 @ X32 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
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
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
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
    inference(demod,[status(thm)],['64','65','66','67','68','69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
        | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['56','76'])).

thf('78',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['43','77'])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['30','79'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('84',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('87',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['88','89'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('92',plain,(
    l1_struct_0 @ sk_D_1 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['57'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('103',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['57'])).

thf('104',plain,(
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

thf('105',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( r1_tmap_1 @ X23 @ X25 @ ( k2_tmap_1 @ X22 @ X25 @ X26 @ X23 ) @ X24 )
      | ( X27 != X24 )
      | ~ ( r1_tmap_1 @ X22 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('106',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ X22 @ X25 @ X26 @ X24 )
      | ( r1_tmap_1 @ X23 @ X25 @ ( k2_tmap_1 @ X22 @ X25 @ X26 @ X23 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
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
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['102','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','100','101','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bFkJE5pjLH
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:35:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.34/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.56  % Solved by: fo/fo7.sh
% 0.34/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.56  % done 147 iterations in 0.103s
% 0.34/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.56  % SZS output start Refutation
% 0.34/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.34/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.34/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.34/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.34/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.34/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.34/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.34/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.34/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.34/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.34/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.34/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.34/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.56  thf(t67_tmap_1, conjecture,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.56       ( ![B:$i]:
% 0.34/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.34/0.56             ( l1_pre_topc @ B ) ) =>
% 0.34/0.56           ( ![C:$i]:
% 0.34/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.34/0.56                 ( m1_subset_1 @
% 0.34/0.56                   C @ 
% 0.34/0.56                   ( k1_zfmisc_1 @
% 0.34/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.34/0.56               ( ![D:$i]:
% 0.34/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.34/0.56                     ( m1_pre_topc @ D @ B ) ) =>
% 0.34/0.56                   ( ![E:$i]:
% 0.34/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.34/0.56                       ( ![F:$i]:
% 0.34/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.34/0.56                           ( ( ( E ) = ( F ) ) =>
% 0.34/0.56                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.34/0.56                               ( r1_tmap_1 @
% 0.34/0.56                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.56    (~( ![A:$i]:
% 0.34/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.56            ( l1_pre_topc @ A ) ) =>
% 0.34/0.56          ( ![B:$i]:
% 0.34/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.34/0.56                ( l1_pre_topc @ B ) ) =>
% 0.34/0.56              ( ![C:$i]:
% 0.34/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.56                    ( v1_funct_2 @
% 0.34/0.56                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.34/0.56                    ( m1_subset_1 @
% 0.34/0.56                      C @ 
% 0.34/0.56                      ( k1_zfmisc_1 @
% 0.34/0.56                        ( k2_zfmisc_1 @
% 0.34/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.34/0.56                  ( ![D:$i]:
% 0.34/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.34/0.56                        ( m1_pre_topc @ D @ B ) ) =>
% 0.34/0.56                      ( ![E:$i]:
% 0.34/0.56                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.34/0.56                          ( ![F:$i]:
% 0.34/0.56                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.34/0.56                              ( ( ( E ) = ( F ) ) =>
% 0.34/0.56                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.34/0.56                                  ( r1_tmap_1 @
% 0.34/0.56                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.34/0.56    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.34/0.56  thf('0', plain,
% 0.34/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.34/0.56        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('1', plain,
% 0.34/0.56      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.34/0.56       ~
% 0.34/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.34/0.56      inference('split', [status(esa)], ['0'])).
% 0.34/0.56  thf('2', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('3', plain, (((sk_E) = (sk_F))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.34/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.34/0.56  thf(d2_subset_1, axiom,
% 0.34/0.56    (![A:$i,B:$i]:
% 0.34/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.34/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.34/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.34/0.56  thf('5', plain,
% 0.34/0.56      (![X0 : $i, X1 : $i]:
% 0.34/0.56         (~ (m1_subset_1 @ X0 @ X1)
% 0.34/0.56          | (r2_hidden @ X0 @ X1)
% 0.34/0.56          | (v1_xboole_0 @ X1))),
% 0.34/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.34/0.56  thf('6', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.56  thf('7', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('8', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf(t1_tsep_1, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( l1_pre_topc @ A ) =>
% 0.34/0.56       ( ![B:$i]:
% 0.34/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.34/0.56           ( m1_subset_1 @
% 0.34/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.34/0.56  thf('9', plain,
% 0.34/0.56      (![X20 : $i, X21 : $i]:
% 0.34/0.56         (~ (m1_pre_topc @ X20 @ X21)
% 0.34/0.56          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.34/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.34/0.56          | ~ (l1_pre_topc @ X21))),
% 0.34/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.34/0.56  thf('10', plain,
% 0.34/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.34/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.34/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.34/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.56  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('12', plain,
% 0.34/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.34/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.34/0.56  thf(t9_connsp_2, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.56       ( ![B:$i]:
% 0.34/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.34/0.56             ( ![C:$i]:
% 0.34/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.56                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.34/0.56                      ( ![D:$i]:
% 0.34/0.56                        ( ( m1_subset_1 @
% 0.34/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.56                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.34/0.56                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.56  thf('13', plain,
% 0.34/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.56          | ~ (v3_pre_topc @ X13 @ X14)
% 0.34/0.56          | (m1_connsp_2 @ (sk_D @ X15 @ X13 @ X14) @ X14 @ X15)
% 0.34/0.56          | ~ (r2_hidden @ X15 @ X13)
% 0.34/0.56          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.34/0.56          | ~ (l1_pre_topc @ X14)
% 0.34/0.56          | ~ (v2_pre_topc @ X14)
% 0.34/0.56          | (v2_struct_0 @ X14))),
% 0.34/0.56      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.34/0.56  thf('14', plain,
% 0.34/0.56      (![X0 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56             sk_B @ X0)
% 0.34/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.56  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('17', plain,
% 0.34/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.34/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.34/0.56  thf(t16_tsep_1, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.56       ( ![B:$i]:
% 0.34/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.34/0.56           ( ![C:$i]:
% 0.34/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.34/0.56                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.34/0.56                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.34/0.56  thf('18', plain,
% 0.34/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.34/0.56         (~ (m1_pre_topc @ X17 @ X18)
% 0.34/0.56          | ((X19) != (u1_struct_0 @ X17))
% 0.34/0.56          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.34/0.56          | ~ (m1_pre_topc @ X17 @ X18)
% 0.34/0.56          | (v3_pre_topc @ X19 @ X18)
% 0.34/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.34/0.56          | ~ (l1_pre_topc @ X18)
% 0.34/0.56          | ~ (v2_pre_topc @ X18))),
% 0.34/0.56      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.34/0.56  thf('19', plain,
% 0.34/0.56      (![X17 : $i, X18 : $i]:
% 0.34/0.56         (~ (v2_pre_topc @ X18)
% 0.34/0.56          | ~ (l1_pre_topc @ X18)
% 0.34/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.34/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.34/0.56          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.34/0.56          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.34/0.56          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.34/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.34/0.56  thf('20', plain,
% 0.34/0.56      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.34/0.56        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.34/0.56        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.34/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.34/0.56        | ~ (v2_pre_topc @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['17', '19'])).
% 0.34/0.56  thf('21', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('22', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('24', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('25', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.34/0.56      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.34/0.56  thf('26', plain,
% 0.34/0.56      (![X0 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56             sk_B @ X0))),
% 0.34/0.56      inference('demod', [status(thm)], ['14', '15', '16', '25'])).
% 0.34/0.56  thf('27', plain,
% 0.34/0.56      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.34/0.56         sk_E)
% 0.34/0.56        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (v2_struct_0 @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['7', '26'])).
% 0.34/0.56  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('29', plain,
% 0.34/0.56      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56           sk_B @ sk_E))),
% 0.34/0.56      inference('clc', [status(thm)], ['27', '28'])).
% 0.34/0.56  thf('30', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56           sk_B @ sk_E))),
% 0.34/0.56      inference('sup-', [status(thm)], ['6', '29'])).
% 0.34/0.56  thf('31', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.56  thf('32', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('33', plain,
% 0.34/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.34/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.34/0.56  thf('34', plain,
% 0.34/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.56          | ~ (v3_pre_topc @ X13 @ X14)
% 0.34/0.56          | (r1_tarski @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 0.34/0.56          | ~ (r2_hidden @ X15 @ X13)
% 0.34/0.56          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.34/0.56          | ~ (l1_pre_topc @ X14)
% 0.34/0.56          | ~ (v2_pre_topc @ X14)
% 0.34/0.56          | (v2_struct_0 @ X14))),
% 0.34/0.56      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.34/0.56  thf('35', plain,
% 0.34/0.56      (![X0 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56             (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.56  thf('36', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('38', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.34/0.56      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.34/0.56  thf('39', plain,
% 0.34/0.56      (![X0 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56             (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.34/0.56  thf('40', plain,
% 0.34/0.56      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56         (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (v2_struct_0 @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['32', '39'])).
% 0.34/0.56  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('42', plain,
% 0.34/0.56      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56           (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('clc', [status(thm)], ['40', '41'])).
% 0.34/0.56  thf('43', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56           (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['31', '42'])).
% 0.34/0.56  thf('44', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.56  thf('45', plain,
% 0.34/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.34/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.34/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.34/0.56  thf('46', plain,
% 0.34/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.56          | ~ (v3_pre_topc @ X13 @ X14)
% 0.34/0.56          | (m1_subset_1 @ (sk_D @ X15 @ X13 @ X14) @ 
% 0.34/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.56          | ~ (r2_hidden @ X15 @ X13)
% 0.34/0.56          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.34/0.56          | ~ (l1_pre_topc @ X14)
% 0.34/0.56          | ~ (v2_pre_topc @ X14)
% 0.34/0.56          | (v2_struct_0 @ X14))),
% 0.34/0.56      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.34/0.56  thf('47', plain,
% 0.34/0.56      (![X0 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.34/0.56  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('50', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.34/0.56      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.34/0.56  thf('51', plain,
% 0.34/0.56      (![X0 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.34/0.56      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.34/0.56  thf('52', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.34/0.56        | (v2_struct_0 @ sk_B))),
% 0.34/0.56      inference('sup-', [status(thm)], ['44', '51'])).
% 0.34/0.56  thf('53', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('54', plain,
% 0.34/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56        | (m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56        | (v2_struct_0 @ sk_B))),
% 0.34/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.34/0.56  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('56', plain,
% 0.34/0.56      (((m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.34/0.56      inference('clc', [status(thm)], ['54', '55'])).
% 0.34/0.56  thf('57', plain,
% 0.34/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.34/0.56        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('58', plain,
% 0.34/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('split', [status(esa)], ['57'])).
% 0.34/0.56  thf('59', plain, (((sk_E) = (sk_F))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('60', plain,
% 0.34/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.34/0.56  thf('61', plain,
% 0.34/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.56        (k1_zfmisc_1 @ 
% 0.34/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf(t65_tmap_1, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.56       ( ![B:$i]:
% 0.34/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.34/0.56             ( l1_pre_topc @ B ) ) =>
% 0.34/0.56           ( ![C:$i]:
% 0.34/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.34/0.56                 ( m1_subset_1 @
% 0.34/0.56                   C @ 
% 0.34/0.56                   ( k1_zfmisc_1 @
% 0.34/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.34/0.56               ( ![D:$i]:
% 0.34/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.34/0.56                   ( ![E:$i]:
% 0.34/0.56                     ( ( m1_subset_1 @
% 0.34/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.34/0.56                       ( ![F:$i]:
% 0.34/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.34/0.56                           ( ![G:$i]:
% 0.34/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.34/0.56                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.34/0.56                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.34/0.56                                   ( ( F ) = ( G ) ) ) =>
% 0.34/0.56                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.34/0.56                                   ( r1_tmap_1 @
% 0.34/0.56                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.56  thf('62', plain,
% 0.34/0.56      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.34/0.56         ((v2_struct_0 @ X28)
% 0.34/0.56          | ~ (v2_pre_topc @ X28)
% 0.34/0.56          | ~ (l1_pre_topc @ X28)
% 0.34/0.56          | (v2_struct_0 @ X29)
% 0.34/0.56          | ~ (m1_pre_topc @ X29 @ X28)
% 0.34/0.56          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.34/0.56          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.34/0.56          | ~ (m1_connsp_2 @ X31 @ X28 @ X30)
% 0.34/0.56          | ((X30) != (X32))
% 0.34/0.56          | ~ (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ 
% 0.34/0.56               X32)
% 0.34/0.56          | (r1_tmap_1 @ X28 @ X33 @ X34 @ X30)
% 0.34/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.34/0.56          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.34/0.56          | ~ (m1_subset_1 @ X34 @ 
% 0.34/0.56               (k1_zfmisc_1 @ 
% 0.34/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.34/0.56          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.34/0.56          | ~ (v1_funct_1 @ X34)
% 0.34/0.56          | ~ (l1_pre_topc @ X33)
% 0.34/0.56          | ~ (v2_pre_topc @ X33)
% 0.34/0.56          | (v2_struct_0 @ X33))),
% 0.34/0.56      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.34/0.56  thf('63', plain,
% 0.34/0.56      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.34/0.56         ((v2_struct_0 @ X33)
% 0.34/0.56          | ~ (v2_pre_topc @ X33)
% 0.34/0.56          | ~ (l1_pre_topc @ X33)
% 0.34/0.56          | ~ (v1_funct_1 @ X34)
% 0.34/0.56          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.34/0.56          | ~ (m1_subset_1 @ X34 @ 
% 0.34/0.56               (k1_zfmisc_1 @ 
% 0.34/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.34/0.56          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.34/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.34/0.56          | (r1_tmap_1 @ X28 @ X33 @ X34 @ X32)
% 0.34/0.56          | ~ (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ 
% 0.34/0.56               X32)
% 0.34/0.56          | ~ (m1_connsp_2 @ X31 @ X28 @ X32)
% 0.34/0.56          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.34/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.34/0.56          | ~ (m1_pre_topc @ X29 @ X28)
% 0.34/0.56          | (v2_struct_0 @ X29)
% 0.34/0.56          | ~ (l1_pre_topc @ X28)
% 0.34/0.56          | ~ (v2_pre_topc @ X28)
% 0.34/0.56          | (v2_struct_0 @ X28))),
% 0.34/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.34/0.56  thf('64', plain,
% 0.34/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.34/0.56          | (v2_struct_0 @ X0)
% 0.34/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.34/0.56          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.34/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.34/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.34/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.56               (u1_struct_0 @ sk_A))
% 0.34/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.34/0.56          | (v2_struct_0 @ sk_A))),
% 0.34/0.56      inference('sup-', [status(thm)], ['61', '63'])).
% 0.34/0.56  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('67', plain,
% 0.34/0.56      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('71', plain,
% 0.34/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | (v2_struct_0 @ X0)
% 0.34/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.34/0.56          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.34/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.34/0.56          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.34/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56          | (v2_struct_0 @ sk_A))),
% 0.34/0.56      inference('demod', [status(thm)],
% 0.34/0.56                ['64', '65', '66', '67', '68', '69', '70'])).
% 0.34/0.56  thf('72', plain,
% 0.34/0.56      ((![X0 : $i]:
% 0.34/0.56          ((v2_struct_0 @ sk_A)
% 0.34/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.34/0.56           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.34/0.56           | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.34/0.56           | (v2_struct_0 @ sk_D_1)
% 0.34/0.56           | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['60', '71'])).
% 0.34/0.56  thf('73', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.34/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.34/0.56  thf('74', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('75', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('76', plain,
% 0.34/0.56      ((![X0 : $i]:
% 0.34/0.56          ((v2_struct_0 @ sk_A)
% 0.34/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.34/0.56           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56           | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.34/0.56           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56           | (v2_struct_0 @ sk_D_1)
% 0.34/0.56           | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.34/0.56  thf('77', plain,
% 0.34/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56         | (v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | ~ (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56              (u1_struct_0 @ sk_D_1))
% 0.34/0.56         | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56              sk_B @ sk_E)
% 0.34/0.56         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_A)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['56', '76'])).
% 0.34/0.56  thf('78', plain,
% 0.34/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56         | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56              sk_B @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (v2_struct_0 @ sk_B)
% 0.34/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['43', '77'])).
% 0.34/0.56  thf('79', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.34/0.56              sk_B @ sk_E)
% 0.34/0.56         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('simplify', [status(thm)], ['78'])).
% 0.34/0.56  thf('80', plain,
% 0.34/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['30', '79'])).
% 0.34/0.56  thf('81', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('simplify', [status(thm)], ['80'])).
% 0.34/0.56  thf('82', plain,
% 0.34/0.56      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('split', [status(esa)], ['0'])).
% 0.34/0.56  thf('83', plain,
% 0.34/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.34/0.56  thf(fc2_struct_0, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.34/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.34/0.56  thf('84', plain,
% 0.34/0.56      (![X6 : $i]:
% 0.34/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.34/0.56          | ~ (l1_struct_0 @ X6)
% 0.34/0.56          | (v2_struct_0 @ X6))),
% 0.34/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.34/0.56  thf('85', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | ~ (l1_struct_0 @ sk_D_1)))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.34/0.56  thf('86', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf(dt_m1_pre_topc, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( l1_pre_topc @ A ) =>
% 0.34/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.34/0.56  thf('87', plain,
% 0.34/0.56      (![X4 : $i, X5 : $i]:
% 0.34/0.56         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.34/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.34/0.56  thf('88', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.34/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.34/0.56  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('90', plain, ((l1_pre_topc @ sk_D_1)),
% 0.34/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.34/0.56  thf(dt_l1_pre_topc, axiom,
% 0.34/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.34/0.56  thf('91', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.34/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.34/0.56  thf('92', plain, ((l1_struct_0 @ sk_D_1)),
% 0.34/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.34/0.56  thf('93', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (v2_struct_0 @ sk_A)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('demod', [status(thm)], ['85', '92'])).
% 0.34/0.56  thf('94', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('simplify', [status(thm)], ['93'])).
% 0.34/0.56  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('96', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('clc', [status(thm)], ['94', '95'])).
% 0.34/0.56  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('98', plain,
% 0.34/0.56      (((v2_struct_0 @ sk_D_1))
% 0.34/0.56         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('clc', [status(thm)], ['96', '97'])).
% 0.34/0.56  thf('99', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('100', plain,
% 0.34/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.34/0.56       ~
% 0.34/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.34/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.34/0.56  thf('101', plain,
% 0.34/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.34/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.34/0.56      inference('split', [status(esa)], ['57'])).
% 0.34/0.56  thf('102', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.34/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.34/0.56  thf('103', plain,
% 0.34/0.56      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('split', [status(esa)], ['57'])).
% 0.34/0.56  thf('104', plain,
% 0.34/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.56        (k1_zfmisc_1 @ 
% 0.34/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf(t64_tmap_1, axiom,
% 0.34/0.56    (![A:$i]:
% 0.34/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.56       ( ![B:$i]:
% 0.34/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.34/0.56             ( l1_pre_topc @ B ) ) =>
% 0.34/0.56           ( ![C:$i]:
% 0.34/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.34/0.56                 ( m1_subset_1 @
% 0.34/0.56                   C @ 
% 0.34/0.56                   ( k1_zfmisc_1 @
% 0.34/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.34/0.56               ( ![D:$i]:
% 0.34/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.34/0.56                   ( ![E:$i]:
% 0.34/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.34/0.56                       ( ![F:$i]:
% 0.34/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.34/0.56                           ( ( ( ( E ) = ( F ) ) & 
% 0.34/0.56                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.34/0.56                             ( r1_tmap_1 @
% 0.34/0.56                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.56  thf('105', plain,
% 0.34/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.56         ((v2_struct_0 @ X22)
% 0.34/0.56          | ~ (v2_pre_topc @ X22)
% 0.34/0.56          | ~ (l1_pre_topc @ X22)
% 0.34/0.56          | (v2_struct_0 @ X23)
% 0.34/0.56          | ~ (m1_pre_topc @ X23 @ X22)
% 0.34/0.56          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.34/0.56          | (r1_tmap_1 @ X23 @ X25 @ (k2_tmap_1 @ X22 @ X25 @ X26 @ X23) @ X24)
% 0.34/0.56          | ((X27) != (X24))
% 0.34/0.56          | ~ (r1_tmap_1 @ X22 @ X25 @ X26 @ X27)
% 0.34/0.56          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X22))
% 0.34/0.56          | ~ (m1_subset_1 @ X26 @ 
% 0.34/0.56               (k1_zfmisc_1 @ 
% 0.34/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))))
% 0.34/0.56          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))
% 0.34/0.56          | ~ (v1_funct_1 @ X26)
% 0.34/0.56          | ~ (l1_pre_topc @ X25)
% 0.34/0.56          | ~ (v2_pre_topc @ X25)
% 0.34/0.56          | (v2_struct_0 @ X25))),
% 0.34/0.56      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.34/0.56  thf('106', plain,
% 0.34/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.34/0.56         ((v2_struct_0 @ X25)
% 0.34/0.56          | ~ (v2_pre_topc @ X25)
% 0.34/0.56          | ~ (l1_pre_topc @ X25)
% 0.34/0.56          | ~ (v1_funct_1 @ X26)
% 0.34/0.56          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))
% 0.34/0.56          | ~ (m1_subset_1 @ X26 @ 
% 0.34/0.56               (k1_zfmisc_1 @ 
% 0.34/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25))))
% 0.34/0.56          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.34/0.56          | ~ (r1_tmap_1 @ X22 @ X25 @ X26 @ X24)
% 0.34/0.56          | (r1_tmap_1 @ X23 @ X25 @ (k2_tmap_1 @ X22 @ X25 @ X26 @ X23) @ X24)
% 0.34/0.56          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.34/0.56          | ~ (m1_pre_topc @ X23 @ X22)
% 0.34/0.56          | (v2_struct_0 @ X23)
% 0.34/0.56          | ~ (l1_pre_topc @ X22)
% 0.34/0.56          | ~ (v2_pre_topc @ X22)
% 0.34/0.56          | (v2_struct_0 @ X22))),
% 0.34/0.56      inference('simplify', [status(thm)], ['105'])).
% 0.34/0.56  thf('107', plain,
% 0.34/0.56      (![X0 : $i, X1 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.34/0.56          | (v2_struct_0 @ X0)
% 0.34/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.34/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.34/0.56             X1)
% 0.34/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.56               (u1_struct_0 @ sk_A))
% 0.34/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.34/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.34/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.34/0.56          | (v2_struct_0 @ sk_A))),
% 0.34/0.56      inference('sup-', [status(thm)], ['104', '106'])).
% 0.34/0.56  thf('108', plain, ((v2_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('110', plain,
% 0.34/0.56      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('111', plain, ((v1_funct_1 @ sk_C_1)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('114', plain,
% 0.34/0.56      (![X0 : $i, X1 : $i]:
% 0.34/0.56         ((v2_struct_0 @ sk_B)
% 0.34/0.56          | (v2_struct_0 @ X0)
% 0.34/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.34/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.34/0.56             X1)
% 0.34/0.56          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.34/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.34/0.56          | (v2_struct_0 @ sk_A))),
% 0.34/0.56      inference('demod', [status(thm)],
% 0.34/0.56                ['107', '108', '109', '110', '111', '112', '113'])).
% 0.34/0.56  thf('115', plain,
% 0.34/0.56      ((![X0 : $i]:
% 0.34/0.56          ((v2_struct_0 @ sk_A)
% 0.34/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.34/0.56           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.34/0.56              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.34/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.34/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.34/0.56           | (v2_struct_0 @ X0)
% 0.34/0.56           | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['103', '114'])).
% 0.34/0.56  thf('116', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('117', plain,
% 0.34/0.56      ((![X0 : $i]:
% 0.34/0.56          ((v2_struct_0 @ sk_A)
% 0.34/0.56           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.34/0.56              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.34/0.56           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.34/0.56           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.34/0.56           | (v2_struct_0 @ X0)
% 0.34/0.56           | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('demod', [status(thm)], ['115', '116'])).
% 0.34/0.56  thf('118', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.34/0.56         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_A)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['102', '117'])).
% 0.34/0.56  thf('119', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('120', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B)
% 0.34/0.56         | (v2_struct_0 @ sk_D_1)
% 0.34/0.56         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.34/0.56         | (v2_struct_0 @ sk_A)))
% 0.34/0.56         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('demod', [status(thm)], ['118', '119'])).
% 0.34/0.56  thf('121', plain,
% 0.34/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.34/0.56         <= (~
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('split', [status(esa)], ['0'])).
% 0.34/0.56  thf('122', plain, (((sk_E) = (sk_F))),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('123', plain,
% 0.34/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.34/0.56         <= (~
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.34/0.56      inference('demod', [status(thm)], ['121', '122'])).
% 0.34/0.56  thf('124', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.34/0.56         <= (~
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('sup-', [status(thm)], ['120', '123'])).
% 0.34/0.56  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('126', plain,
% 0.34/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.34/0.56         <= (~
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('clc', [status(thm)], ['124', '125'])).
% 0.34/0.56  thf('127', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('128', plain,
% 0.34/0.56      (((v2_struct_0 @ sk_D_1))
% 0.34/0.56         <= (~
% 0.34/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.34/0.56             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.34/0.56      inference('clc', [status(thm)], ['126', '127'])).
% 0.34/0.56  thf('129', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.34/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.56  thf('130', plain,
% 0.34/0.56      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.34/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.34/0.56         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.34/0.56      inference('sup-', [status(thm)], ['128', '129'])).
% 0.34/0.56  thf('131', plain, ($false),
% 0.34/0.56      inference('sat_resolution*', [status(thm)], ['1', '100', '101', '130'])).
% 0.34/0.56  
% 0.34/0.56  % SZS output end Refutation
% 0.34/0.56  
% 0.34/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
