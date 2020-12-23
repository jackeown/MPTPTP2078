%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hc4JDMcaNx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:23 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 806 expanded)
%              Number of leaves         :   39 ( 242 expanded)
%              Depth                    :   32
%              Number of atoms          : 2493 (27295 expanded)
%              Number of equality atoms :   11 ( 343 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t86_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_tsep_1 @ C @ D )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

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

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( m1_connsp_2 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

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

thf('27',plain,(
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

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D_1 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_tsep_1 @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('34',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

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

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tarski @ ( sk_D @ X16 @ X14 @ X15 ) @ X16 )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('44',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( m1_connsp_2 @ ( sk_D @ X16 @ X14 @ X15 ) @ X15 @ X14 )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('56',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('64',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( sk_D @ X16 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('68',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X26 @ X29 )
      | ~ ( r1_tmap_1 @ X29 @ X25 @ X30 @ X28 )
      | ( X28 != X31 )
      | ( r1_tmap_1 @ X26 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('86',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30 ) @ X31 )
      | ~ ( r1_tmap_1 @ X29 @ X25 @ X30 @ X31 )
      | ~ ( m1_pre_topc @ X26 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['82','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['81','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['79'])).

thf('105',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('117',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['80','115','116'])).

thf('118',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['78','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('120',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X39 )
      | ( X39 != X37 )
      | ~ ( m1_connsp_2 @ X36 @ X33 @ X39 )
      | ~ ( r1_tarski @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('121',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r1_tarski @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_connsp_2 @ X36 @ X33 @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X37 )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('134',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['79'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['80','115'])).

thf('144',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('146',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['150','151'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('153',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('154',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['147','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['0','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hc4JDMcaNx
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 158 iterations in 0.109s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.39/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.57  thf(t86_tmap_1, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57             ( l1_pre_topc @ B ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57               ( ![D:$i]:
% 0.39/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                   ( ![E:$i]:
% 0.39/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                         ( v1_funct_2 @
% 0.39/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                         ( m1_subset_1 @
% 0.39/0.57                           E @ 
% 0.39/0.57                           ( k1_zfmisc_1 @
% 0.39/0.57                             ( k2_zfmisc_1 @
% 0.39/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.39/0.57                         ( ![F:$i]:
% 0.39/0.57                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.57                             ( ![G:$i]:
% 0.39/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.57                                 ( ( ( F ) = ( G ) ) =>
% 0.39/0.57                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.39/0.57                                     ( r1_tmap_1 @
% 0.39/0.57                                       C @ B @ 
% 0.39/0.57                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57            ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57                ( l1_pre_topc @ B ) ) =>
% 0.39/0.57              ( ![C:$i]:
% 0.39/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57                  ( ![D:$i]:
% 0.39/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                      ( ![E:$i]:
% 0.39/0.57                        ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                            ( v1_funct_2 @
% 0.39/0.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                            ( m1_subset_1 @
% 0.39/0.57                              E @ 
% 0.39/0.57                              ( k1_zfmisc_1 @
% 0.39/0.57                                ( k2_zfmisc_1 @
% 0.39/0.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.39/0.57                            ( ![F:$i]:
% 0.39/0.57                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.57                                ( ![G:$i]:
% 0.39/0.57                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.57                                    ( ( ( F ) = ( G ) ) =>
% 0.39/0.57                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.39/0.57                                        ( r1_tmap_1 @
% 0.39/0.57                                          C @ B @ 
% 0.39/0.57                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.39/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('2', plain, (((sk_F) = (sk_G))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(t2_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ X1)
% 0.39/0.57          | (v1_xboole_0 @ X1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t1_tsep_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.57           ( m1_subset_1 @
% 0.39/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X20 @ X21)
% 0.39/0.57          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.57          | ~ (l1_pre_topc @ X21))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_D_1)
% 0.39/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_m1_pre_topc, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.57  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('14', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.57  thf(t5_connsp_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.39/0.57                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.57          | ~ (v3_pre_topc @ X11 @ X12)
% 0.39/0.57          | ~ (r2_hidden @ X13 @ X11)
% 0.39/0.57          | (m1_connsp_2 @ X11 @ X12 @ X13)
% 0.39/0.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.39/0.57          | ~ (l1_pre_topc @ X12)
% 0.39/0.57          | ~ (v2_pre_topc @ X12)
% 0.39/0.57          | (v2_struct_0 @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc1_pre_topc, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X2 @ X3)
% 0.39/0.57          | (v2_pre_topc @ X2)
% 0.39/0.57          | ~ (l1_pre_topc @ X3)
% 0.39/0.57          | ~ (v2_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_pre_topc @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('23', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.57  thf('24', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.57  thf(t16_tsep_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.39/0.57                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.39/0.57                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X17 @ X18)
% 0.39/0.57          | ((X19) != (u1_struct_0 @ X17))
% 0.39/0.57          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.39/0.57          | ~ (m1_pre_topc @ X17 @ X18)
% 0.39/0.57          | (v3_pre_topc @ X19 @ X18)
% 0.39/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.57          | ~ (l1_pre_topc @ X18)
% 0.39/0.57          | ~ (v2_pre_topc @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (~ (v2_pre_topc @ X18)
% 0.39/0.57          | ~ (l1_pre_topc @ X18)
% 0.39/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.57          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.39/0.57          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.39/0.57          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.39/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      ((~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.57        | ~ (v1_tsep_1 @ sk_C @ sk_D_1)
% 0.39/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.57        | ~ (v2_pre_topc @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['26', '28'])).
% 0.39/0.57  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('31', plain, ((v1_tsep_1 @ sk_C @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('32', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('33', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.57  thf('34', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '35'])).
% 0.39/0.57  thf('37', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (((m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F)
% 0.39/0.57        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('clc', [status(thm)], ['36', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.57  thf(t7_connsp_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.39/0.57                    ( ![D:$i]:
% 0.39/0.57                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.39/0.57                          ( m1_subset_1 @
% 0.39/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.57                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.39/0.57                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.39/0.57          | (r1_tarski @ (sk_D @ X16 @ X14 @ X15) @ X16)
% 0.39/0.57          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.39/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.57          | ~ (l1_pre_topc @ X15)
% 0.39/0.57          | ~ (v2_pre_topc @ X15)
% 0.39/0.57          | (v2_struct_0 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ X0 @ sk_D_1) @ 
% 0.39/0.57             (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.57  thf('44', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ X0 @ sk_D_1) @ 
% 0.39/0.57             (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57           (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '45'])).
% 0.39/0.57  thf('47', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57           (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.57  thf('49', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57         (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('clc', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '38'])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.39/0.57          | (m1_connsp_2 @ (sk_D @ X16 @ X14 @ X15) @ X15 @ X14)
% 0.39/0.57          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.39/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.57          | ~ (l1_pre_topc @ X15)
% 0.39/0.57          | ~ (v2_pre_topc @ X15)
% 0.39/0.57          | (v2_struct_0 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_C) @ X0 @ sk_D_1) @ 
% 0.39/0.57             sk_D_1 @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.57  thf('55', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.57  thf('56', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_C) @ X0 @ sk_D_1) @ 
% 0.39/0.57             sk_D_1 @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57           sk_D_1 @ sk_F)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['51', '57'])).
% 0.39/0.57  thf('59', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57           sk_D_1 @ sk_F)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.57  thf('61', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57         sk_D_1 @ sk_F)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('clc', [status(thm)], ['60', '61'])).
% 0.39/0.57  thf('63', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '38'])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.57  thf('65', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.39/0.57          | (m1_subset_1 @ (sk_D @ X16 @ X14 @ X15) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.57          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.39/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.57          | ~ (l1_pre_topc @ X15)
% 0.39/0.57          | ~ (v2_pre_topc @ X15)
% 0.39/0.57          | (v2_struct_0 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.57          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C) @ X0 @ sk_D_1) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.57  thf('67', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.57  thf('68', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.57          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C) @ X0 @ sk_D_1) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['63', '69'])).
% 0.39/0.57  thf('71', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('72', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.39/0.57  thf('73', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('74', plain,
% 0.39/0.57      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('clc', [status(thm)], ['72', '73'])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)
% 0.39/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('76', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.39/0.57      inference('split', [status(esa)], ['75'])).
% 0.39/0.57  thf('77', plain, (((sk_F) = (sk_G))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.39/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.57  thf('79', plain,
% 0.39/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)
% 0.39/0.57        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('80', plain,
% 0.39/0.57      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)) | 
% 0.39/0.57       ~
% 0.39/0.57       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))),
% 0.39/0.57      inference('split', [status(esa)], ['79'])).
% 0.39/0.57  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('82', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('83', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('split', [status(esa)], ['75'])).
% 0.39/0.57  thf('84', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t81_tmap_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57             ( l1_pre_topc @ B ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57               ( ![D:$i]:
% 0.39/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                   ( ![E:$i]:
% 0.39/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                         ( v1_funct_2 @
% 0.39/0.57                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                         ( m1_subset_1 @
% 0.39/0.57                           E @ 
% 0.39/0.57                           ( k1_zfmisc_1 @
% 0.39/0.57                             ( k2_zfmisc_1 @
% 0.39/0.57                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                       ( ![F:$i]:
% 0.39/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.57                           ( ![G:$i]:
% 0.39/0.57                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.57                               ( ( ( ( F ) = ( G ) ) & 
% 0.39/0.57                                   ( m1_pre_topc @ D @ C ) & 
% 0.39/0.57                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.39/0.57                                 ( r1_tmap_1 @
% 0.39/0.57                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.39/0.57                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('85', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X25)
% 0.39/0.57          | ~ (v2_pre_topc @ X25)
% 0.39/0.57          | ~ (l1_pre_topc @ X25)
% 0.39/0.57          | (v2_struct_0 @ X26)
% 0.39/0.57          | ~ (m1_pre_topc @ X26 @ X27)
% 0.39/0.57          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.39/0.57          | ~ (m1_pre_topc @ X26 @ X29)
% 0.39/0.57          | ~ (r1_tmap_1 @ X29 @ X25 @ X30 @ X28)
% 0.39/0.57          | ((X28) != (X31))
% 0.39/0.57          | (r1_tmap_1 @ X26 @ X25 @ 
% 0.39/0.57             (k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30) @ X31)
% 0.39/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.39/0.57          | ~ (m1_subset_1 @ X30 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))))
% 0.39/0.57          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))
% 0.39/0.57          | ~ (v1_funct_1 @ X30)
% 0.39/0.57          | ~ (m1_pre_topc @ X29 @ X27)
% 0.39/0.57          | (v2_struct_0 @ X29)
% 0.39/0.57          | ~ (l1_pre_topc @ X27)
% 0.39/0.57          | ~ (v2_pre_topc @ X27)
% 0.39/0.57          | (v2_struct_0 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.39/0.57  thf('86', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X27)
% 0.39/0.57          | ~ (v2_pre_topc @ X27)
% 0.39/0.57          | ~ (l1_pre_topc @ X27)
% 0.39/0.57          | (v2_struct_0 @ X29)
% 0.39/0.57          | ~ (m1_pre_topc @ X29 @ X27)
% 0.39/0.57          | ~ (v1_funct_1 @ X30)
% 0.39/0.57          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))
% 0.39/0.57          | ~ (m1_subset_1 @ X30 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))))
% 0.39/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.39/0.57          | (r1_tmap_1 @ X26 @ X25 @ 
% 0.39/0.57             (k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30) @ X31)
% 0.39/0.57          | ~ (r1_tmap_1 @ X29 @ X25 @ X30 @ X31)
% 0.39/0.57          | ~ (m1_pre_topc @ X26 @ X29)
% 0.39/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.39/0.57          | ~ (m1_pre_topc @ X26 @ X27)
% 0.39/0.57          | (v2_struct_0 @ X26)
% 0.39/0.57          | ~ (l1_pre_topc @ X25)
% 0.39/0.57          | ~ (v2_pre_topc @ X25)
% 0.39/0.57          | (v2_struct_0 @ X25))),
% 0.39/0.57      inference('simplify', [status(thm)], ['85'])).
% 0.39/0.57  thf('87', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.39/0.57          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.39/0.57          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.39/0.57             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.39/0.57          | (v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (l1_pre_topc @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X1)
% 0.39/0.57          | (v2_struct_0 @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['84', '86'])).
% 0.39/0.57  thf('88', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('90', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('92', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.39/0.57          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.39/0.57          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.39/0.57             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.39/0.57          | (v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (l1_pre_topc @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X1)
% 0.39/0.57          | (v2_struct_0 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.39/0.57  thf('93', plain,
% 0.39/0.57      ((![X0 : $i, X1 : $i]:
% 0.39/0.57          ((v2_struct_0 @ X0)
% 0.39/0.57           | ~ (v2_pre_topc @ X0)
% 0.39/0.57           | ~ (l1_pre_topc @ X0)
% 0.39/0.57           | (v2_struct_0 @ sk_D_1)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.57           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.39/0.57           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.39/0.57           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.57           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.57           | (v2_struct_0 @ X1)
% 0.39/0.57           | (v2_struct_0 @ sk_B)))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['83', '92'])).
% 0.39/0.57  thf('94', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      ((![X0 : $i, X1 : $i]:
% 0.39/0.57          ((v2_struct_0 @ X0)
% 0.39/0.57           | ~ (v2_pre_topc @ X0)
% 0.39/0.57           | ~ (l1_pre_topc @ X0)
% 0.39/0.57           | (v2_struct_0 @ sk_D_1)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.57           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.39/0.57           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.39/0.57           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.57           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.57           | (v2_struct_0 @ X1)
% 0.39/0.57           | (v2_struct_0 @ sk_B)))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['93', '94'])).
% 0.39/0.57  thf('96', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((v2_struct_0 @ sk_B)
% 0.39/0.57           | (v2_struct_0 @ sk_C)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.57           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.57           | (v2_struct_0 @ sk_D_1)
% 0.39/0.57           | ~ (l1_pre_topc @ X0)
% 0.39/0.57           | ~ (v2_pre_topc @ X0)
% 0.39/0.57           | (v2_struct_0 @ X0)))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['82', '95'])).
% 0.39/0.57  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('98', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((v2_struct_0 @ sk_B)
% 0.39/0.57           | (v2_struct_0 @ sk_C)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.39/0.57           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.57           | (v2_struct_0 @ sk_D_1)
% 0.39/0.57           | ~ (l1_pre_topc @ X0)
% 0.39/0.57           | ~ (v2_pre_topc @ X0)
% 0.39/0.57           | (v2_struct_0 @ X0)))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['96', '97'])).
% 0.39/0.57  thf('99', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_A)
% 0.39/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57         | (v2_struct_0 @ sk_D_1)
% 0.39/0.57         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.39/0.57         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.39/0.57         | (v2_struct_0 @ sk_C)
% 0.39/0.57         | (v2_struct_0 @ sk_B)))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['81', '98'])).
% 0.39/0.57  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('102', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('103', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_A)
% 0.39/0.57         | (v2_struct_0 @ sk_D_1)
% 0.39/0.57         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.39/0.57         | (v2_struct_0 @ sk_C)
% 0.39/0.57         | (v2_struct_0 @ sk_B)))
% 0.39/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.39/0.57  thf('104', plain,
% 0.39/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))
% 0.39/0.57         <= (~
% 0.39/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.39/0.57      inference('split', [status(esa)], ['79'])).
% 0.39/0.57  thf('105', plain, (((sk_F) = (sk_G))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('106', plain,
% 0.39/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F))
% 0.39/0.57         <= (~
% 0.39/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.39/0.57      inference('demod', [status(thm)], ['104', '105'])).
% 0.39/0.57  thf('107', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_B)
% 0.39/0.57         | (v2_struct_0 @ sk_C)
% 0.39/0.57         | (v2_struct_0 @ sk_D_1)
% 0.39/0.57         | (v2_struct_0 @ sk_A)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.39/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['103', '106'])).
% 0.39/0.57  thf('108', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('109', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.39/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['107', '108'])).
% 0.39/0.57  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('111', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.39/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('clc', [status(thm)], ['109', '110'])).
% 0.39/0.57  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('113', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_C))
% 0.39/0.57         <= (~
% 0.39/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.39/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('clc', [status(thm)], ['111', '112'])).
% 0.39/0.57  thf('114', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('115', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) | 
% 0.39/0.57       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.39/0.57      inference('sup-', [status(thm)], ['113', '114'])).
% 0.39/0.57  thf('116', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) | 
% 0.39/0.57       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.39/0.57      inference('split', [status(esa)], ['75'])).
% 0.39/0.57  thf('117', plain,
% 0.39/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['80', '115', '116'])).
% 0.39/0.57  thf('118', plain,
% 0.39/0.57      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.57        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['78', '117'])).
% 0.39/0.57  thf('119', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t83_tmap_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57             ( l1_pre_topc @ B ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57               ( ![D:$i]:
% 0.39/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                   ( ![E:$i]:
% 0.39/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                         ( v1_funct_2 @
% 0.39/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                         ( m1_subset_1 @
% 0.39/0.57                           E @ 
% 0.39/0.57                           ( k1_zfmisc_1 @
% 0.39/0.57                             ( k2_zfmisc_1 @
% 0.39/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.57                         ( ![F:$i]:
% 0.39/0.57                           ( ( m1_subset_1 @
% 0.39/0.57                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.57                             ( ![G:$i]:
% 0.39/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.57                                 ( ![H:$i]:
% 0.39/0.57                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.57                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.57                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.39/0.57                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.57                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.57                                         ( r1_tmap_1 @
% 0.39/0.57                                           C @ B @ 
% 0.39/0.57                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.57                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('120', plain,
% 0.39/0.57      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.39/0.57         X39 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X32)
% 0.39/0.57          | ~ (v2_pre_topc @ X32)
% 0.39/0.57          | ~ (l1_pre_topc @ X32)
% 0.39/0.57          | (v2_struct_0 @ X33)
% 0.39/0.57          | ~ (m1_pre_topc @ X33 @ X34)
% 0.39/0.57          | ~ (m1_pre_topc @ X35 @ X33)
% 0.39/0.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.39/0.57          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.39/0.57          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 0.39/0.57               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 0.39/0.57          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X39)
% 0.39/0.57          | ((X39) != (X37))
% 0.39/0.57          | ~ (m1_connsp_2 @ X36 @ X33 @ X39)
% 0.39/0.57          | ~ (r1_tarski @ X36 @ (u1_struct_0 @ X35))
% 0.39/0.57          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X33))
% 0.39/0.57          | ~ (m1_subset_1 @ X38 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 0.39/0.57          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 0.39/0.57          | ~ (v1_funct_1 @ X38)
% 0.39/0.57          | ~ (m1_pre_topc @ X35 @ X34)
% 0.39/0.57          | (v2_struct_0 @ X35)
% 0.39/0.57          | ~ (l1_pre_topc @ X34)
% 0.39/0.57          | ~ (v2_pre_topc @ X34)
% 0.39/0.57          | (v2_struct_0 @ X34))),
% 0.39/0.57      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.39/0.57  thf('121', plain,
% 0.39/0.57      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X34)
% 0.39/0.57          | ~ (v2_pre_topc @ X34)
% 0.39/0.57          | ~ (l1_pre_topc @ X34)
% 0.39/0.57          | (v2_struct_0 @ X35)
% 0.39/0.57          | ~ (m1_pre_topc @ X35 @ X34)
% 0.39/0.57          | ~ (v1_funct_1 @ X38)
% 0.39/0.57          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 0.39/0.57          | ~ (m1_subset_1 @ X38 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 0.39/0.57          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X33))
% 0.39/0.57          | ~ (r1_tarski @ X36 @ (u1_struct_0 @ X35))
% 0.39/0.57          | ~ (m1_connsp_2 @ X36 @ X33 @ X37)
% 0.39/0.57          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X37)
% 0.39/0.57          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 0.39/0.57               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 0.39/0.57          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.39/0.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.39/0.57          | ~ (m1_pre_topc @ X35 @ X33)
% 0.39/0.57          | ~ (m1_pre_topc @ X33 @ X34)
% 0.39/0.57          | (v2_struct_0 @ X33)
% 0.39/0.57          | ~ (l1_pre_topc @ X32)
% 0.39/0.57          | ~ (v2_pre_topc @ X32)
% 0.39/0.57          | (v2_struct_0 @ X32))),
% 0.39/0.57      inference('simplify', [status(thm)], ['120'])).
% 0.39/0.57  thf('122', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.57          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.39/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.39/0.57          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.39/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['119', '121'])).
% 0.39/0.57  thf('123', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('125', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('126', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('127', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_D_1)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.57          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.57               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.39/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.39/0.57          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.39/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.39/0.57  thf('128', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_A)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.39/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.39/0.57          | (v2_struct_0 @ sk_D_1)
% 0.39/0.57          | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['118', '127'])).
% 0.39/0.57  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('131', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('132', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('133', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('134', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('135', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('136', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_A)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.39/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.57          | (v2_struct_0 @ sk_D_1)
% 0.39/0.57          | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)],
% 0.39/0.57                ['128', '129', '130', '131', '132', '133', '134', '135'])).
% 0.39/0.57  thf('137', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57             sk_D_1 @ sk_F)
% 0.39/0.57        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57             (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['74', '136'])).
% 0.39/0.57  thf('138', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57             (u1_struct_0 @ sk_C))
% 0.39/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['62', '137'])).
% 0.39/0.57  thf('139', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_C) @ sk_F @ sk_D_1) @ 
% 0.39/0.57             (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['138'])).
% 0.39/0.57  thf('140', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['50', '139'])).
% 0.39/0.57  thf('141', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['140'])).
% 0.39/0.57  thf('142', plain,
% 0.39/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.39/0.57         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.39/0.57      inference('split', [status(esa)], ['79'])).
% 0.39/0.57  thf('143', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['80', '115'])).
% 0.39/0.57  thf('144', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['142', '143'])).
% 0.39/0.57  thf('145', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['141', '144'])).
% 0.39/0.57  thf(fc2_struct_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.57  thf('146', plain,
% 0.39/0.57      (![X7 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.39/0.57          | ~ (l1_struct_0 @ X7)
% 0.39/0.57          | (v2_struct_0 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.57  thf('147', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | ~ (l1_struct_0 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['145', '146'])).
% 0.39/0.57  thf('148', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('149', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.57  thf('150', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.57  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('152', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['150', '151'])).
% 0.39/0.57  thf(dt_l1_pre_topc, axiom,
% 0.39/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.57  thf('153', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('154', plain, ((l1_struct_0 @ sk_C)),
% 0.39/0.57      inference('sup-', [status(thm)], ['152', '153'])).
% 0.39/0.57  thf('155', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['147', '154'])).
% 0.39/0.57  thf('156', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_D_1)
% 0.39/0.57        | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('simplify', [status(thm)], ['155'])).
% 0.39/0.57  thf('157', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('158', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['156', '157'])).
% 0.39/0.57  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('160', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.39/0.57      inference('clc', [status(thm)], ['158', '159'])).
% 0.39/0.57  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('162', plain, ((v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('clc', [status(thm)], ['160', '161'])).
% 0.39/0.57  thf('163', plain, ($false), inference('demod', [status(thm)], ['0', '162'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
