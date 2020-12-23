%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m0wHhCrAPw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 646 expanded)
%              Number of leaves         :   38 ( 197 expanded)
%              Depth                    :   32
%              Number of atoms          : 2393 (22345 expanded)
%              Number of equality atoms :   11 ( 283 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
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
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

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

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ( r1_tarski @ ( sk_D @ X10 @ X8 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) ) ),
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
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v3_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('34',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('41',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ( m1_connsp_2 @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 @ X10 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('46',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ sk_F ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('59',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('60',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('75',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['67'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( r1_tmap_1 @ X24 @ X20 @ X25 @ X23 )
      | ( X23 != X26 )
      | ( r1_tmap_1 @ X21 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('78',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 ) @ X26 )
      | ~ ( r1_tmap_1 @ X24 @ X20 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
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
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
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
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
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
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['74','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['71'])).

thf('97',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['67'])).

thf('109',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['72','107','108'])).

thf('110',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['70','109'])).

thf('111',plain,(
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

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X34 )
      | ( X34 != X32 )
      | ~ ( m1_connsp_2 @ X31 @ X28 @ X34 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('113',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_connsp_2 @ X31 @ X28 @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
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
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('126',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126','127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['71'])).

thf('135',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['72','107'])).

thf('136',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('138',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('142',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['142','143'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('145',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('146',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['0','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m0wHhCrAPw
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:44:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 131 iterations in 0.053s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(t86_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.50                         ( ![F:$i]:
% 0.20/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                             ( ![G:$i]:
% 0.20/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.50                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.50                                     ( r1_tmap_1 @
% 0.20/0.50                                       C @ B @ 
% 0.20/0.50                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51                ( l1_pre_topc @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                      ( ![E:$i]:
% 0.20/0.51                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                            ( v1_funct_2 @
% 0.20/0.51                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                            ( m1_subset_1 @
% 0.20/0.51                              E @ 
% 0.20/0.51                              ( k1_zfmisc_1 @
% 0.20/0.51                                ( k2_zfmisc_1 @
% 0.20/0.51                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.51                            ( ![F:$i]:
% 0.20/0.51                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                ( ![G:$i]:
% 0.20/0.51                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.51                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.51                                        ( r1_tmap_1 @
% 0.20/0.51                                          C @ B @ 
% 0.20/0.51                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ X1)
% 0.20/0.51          | (v1_xboole_0 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.51          | ~ (l1_pre_topc @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_D_1)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf(t9_connsp_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.51             ( ![C:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.51                      ( ![D:$i]:
% 0.20/0.51                        ( ( m1_subset_1 @
% 0.20/0.51                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.20/0.51                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (v3_pre_topc @ X8 @ X9)
% 0.20/0.51          | (r1_tarski @ (sk_D @ X10 @ X8 @ X9) @ X8)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X2 @ X3)
% 0.20/0.51          | (v2_pre_topc @ X2)
% 0.20/0.51          | ~ (l1_pre_topc @ X3)
% 0.20/0.51          | ~ (v2_pre_topc @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v2_pre_topc @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.51  thf('24', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf(t16_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.51                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | ((X14) != (u1_struct_0 @ X12))
% 0.20/0.51          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.20/0.51          | ~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (v3_pre_topc @ X14 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (v2_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v2_pre_topc @ X13)
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.20/0.51          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.20/0.51          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.20/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.20/0.51        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.51        | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.51  thf('30', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('33', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.51  thf('34', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51         (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '35'])).
% 0.20/0.51  thf('37', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51           (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51           (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('41', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (v3_pre_topc @ X8 @ X9)
% 0.20/0.51          | (m1_connsp_2 @ (sk_D @ X10 @ X8 @ X9) @ X9 @ X10)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             sk_D_1 @ X0)
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.51  thf('46', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             sk_D_1 @ X0)
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.51  thf('48', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             sk_D_1 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51         sk_D_1 @ sk_F)
% 0.20/0.51        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '49'])).
% 0.20/0.51  thf('51', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51           sk_D_1 @ sk_F))),
% 0.20/0.51      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51           sk_D_1 @ sk_F))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (v3_pre_topc @ X8 @ X9)
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X10 @ X8 @ X9) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.51  thf('58', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.51  thf('59', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('60', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.51      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '61'])).
% 0.20/0.51  thf('63', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('65', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (((m1_subset_1 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)
% 0.20/0.51        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['67'])).
% 0.20/0.51  thf('69', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)
% 0.20/0.51        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.51      inference('split', [status(esa)], ['71'])).
% 0.20/0.51  thf('73', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('74', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['67'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t81_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ![F:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                           ( ![G:$i]:
% 0.20/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.51                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.51                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.51                                 ( r1_tmap_1 @
% 0.20/0.51                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.51                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X20)
% 0.20/0.51          | ~ (v2_pre_topc @ X20)
% 0.20/0.51          | ~ (l1_pre_topc @ X20)
% 0.20/0.51          | (v2_struct_0 @ X21)
% 0.20/0.51          | ~ (m1_pre_topc @ X21 @ X22)
% 0.20/0.51          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.20/0.51          | ~ (m1_pre_topc @ X21 @ X24)
% 0.20/0.51          | ~ (r1_tmap_1 @ X24 @ X20 @ X25 @ X23)
% 0.20/0.51          | ((X23) != (X26))
% 0.20/0.51          | (r1_tmap_1 @ X21 @ X20 @ 
% 0.20/0.51             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25) @ X26)
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.20/0.51          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.20/0.51          | ~ (v1_funct_1 @ X25)
% 0.20/0.51          | ~ (m1_pre_topc @ X24 @ X22)
% 0.20/0.51          | (v2_struct_0 @ X24)
% 0.20/0.51          | ~ (l1_pre_topc @ X22)
% 0.20/0.51          | ~ (v2_pre_topc @ X22)
% 0.20/0.51          | (v2_struct_0 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X22)
% 0.20/0.51          | ~ (v2_pre_topc @ X22)
% 0.20/0.51          | ~ (l1_pre_topc @ X22)
% 0.20/0.51          | (v2_struct_0 @ X24)
% 0.20/0.51          | ~ (m1_pre_topc @ X24 @ X22)
% 0.20/0.51          | ~ (v1_funct_1 @ X25)
% 0.20/0.51          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.20/0.51          | (r1_tmap_1 @ X21 @ X20 @ 
% 0.20/0.51             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25) @ X26)
% 0.20/0.51          | ~ (r1_tmap_1 @ X24 @ X20 @ X25 @ X26)
% 0.20/0.51          | ~ (m1_pre_topc @ X21 @ X24)
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.20/0.51          | ~ (m1_pre_topc @ X21 @ X22)
% 0.20/0.51          | (v2_struct_0 @ X21)
% 0.20/0.51          | ~ (l1_pre_topc @ X20)
% 0.20/0.51          | ~ (v2_pre_topc @ X20)
% 0.20/0.51          | (v2_struct_0 @ X20))),
% 0.20/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.51             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.51               (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (l1_pre_topc @ X1)
% 0.20/0.51          | ~ (v2_pre_topc @ X1)
% 0.20/0.51          | (v2_struct_0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['76', '78'])).
% 0.20/0.51  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.51             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (l1_pre_topc @ X1)
% 0.20/0.51          | ~ (v2_pre_topc @ X1)
% 0.20/0.51          | (v2_struct_0 @ X1))),
% 0.20/0.51      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      ((![X0 : $i, X1 : $i]:
% 0.20/0.51          ((v2_struct_0 @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D_1)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.51           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51           | (v2_struct_0 @ X1)
% 0.20/0.51           | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['75', '84'])).
% 0.20/0.51  thf('86', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((![X0 : $i, X1 : $i]:
% 0.20/0.51          ((v2_struct_0 @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D_1)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.51           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51           | (v2_struct_0 @ X1)
% 0.20/0.51           | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_struct_0 @ sk_B)
% 0.20/0.51           | (v2_struct_0 @ sk_C_1)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.20/0.51           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D_1)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ X0)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['74', '87'])).
% 0.20/0.51  thf('89', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_struct_0 @ sk_B)
% 0.20/0.51           | (v2_struct_0 @ sk_C_1)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.51           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D_1)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ X0)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A)
% 0.20/0.51         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51         | (v2_struct_0 @ sk_D_1)
% 0.20/0.51         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.20/0.51         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.51         | (v2_struct_0 @ sk_C_1)
% 0.20/0.51         | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['73', '90'])).
% 0.20/0.51  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('94', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A)
% 0.20/0.51         | (v2_struct_0 @ sk_D_1)
% 0.20/0.51         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.20/0.51         | (v2_struct_0 @ sk_C_1)
% 0.20/0.51         | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['71'])).
% 0.20/0.51  thf('97', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('demod', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_C_1)
% 0.20/0.51         | (v2_struct_0 @ sk_D_1)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['95', '98'])).
% 0.20/0.51  thf('100', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.51  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('clc', [status(thm)], ['101', '102'])).
% 0.20/0.51  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C_1))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.20/0.51       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.20/0.51      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.51  thf('108', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.20/0.51       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.20/0.51      inference('split', [status(esa)], ['67'])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['72', '107', '108'])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.20/0.51        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['70', '109'])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t83_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.51                         ( ![F:$i]:
% 0.20/0.51                           ( ( m1_subset_1 @
% 0.20/0.51                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.51                             ( ![G:$i]:
% 0.20/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                 ( ![H:$i]:
% 0.20/0.51                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.51                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.20/0.51                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.51                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.51                                         ( r1_tmap_1 @
% 0.20/0.51                                           C @ B @ 
% 0.20/0.51                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.51                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 0.20/0.51         X34 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X27)
% 0.20/0.51          | ~ (v2_pre_topc @ X27)
% 0.20/0.51          | ~ (l1_pre_topc @ X27)
% 0.20/0.51          | (v2_struct_0 @ X28)
% 0.20/0.51          | ~ (m1_pre_topc @ X28 @ X29)
% 0.20/0.51          | ~ (m1_pre_topc @ X30 @ X28)
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.51          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.20/0.51          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.20/0.51               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.20/0.51          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X34)
% 0.20/0.51          | ((X34) != (X32))
% 0.20/0.51          | ~ (m1_connsp_2 @ X31 @ X28 @ X34)
% 0.20/0.51          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.20/0.51          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X28))
% 0.20/0.51          | ~ (m1_subset_1 @ X33 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.20/0.51          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.20/0.51          | ~ (v1_funct_1 @ X33)
% 0.20/0.51          | ~ (m1_pre_topc @ X30 @ X29)
% 0.20/0.51          | (v2_struct_0 @ X30)
% 0.20/0.51          | ~ (l1_pre_topc @ X29)
% 0.20/0.51          | ~ (v2_pre_topc @ X29)
% 0.20/0.51          | (v2_struct_0 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.20/0.51  thf('113', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X29)
% 0.20/0.51          | ~ (v2_pre_topc @ X29)
% 0.20/0.51          | ~ (l1_pre_topc @ X29)
% 0.20/0.51          | (v2_struct_0 @ X30)
% 0.20/0.51          | ~ (m1_pre_topc @ X30 @ X29)
% 0.20/0.51          | ~ (v1_funct_1 @ X33)
% 0.20/0.51          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.20/0.51          | ~ (m1_subset_1 @ X33 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.20/0.51          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.20/0.51          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.20/0.51          | ~ (m1_connsp_2 @ X31 @ X28 @ X32)
% 0.20/0.51          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 0.20/0.51          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.20/0.51               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.20/0.51          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.51          | ~ (m1_pre_topc @ X30 @ X28)
% 0.20/0.51          | ~ (m1_pre_topc @ X28 @ X29)
% 0.20/0.51          | (v2_struct_0 @ X28)
% 0.20/0.51          | ~ (l1_pre_topc @ X27)
% 0.20/0.51          | ~ (v2_pre_topc @ X27)
% 0.20/0.51          | (v2_struct_0 @ X27))),
% 0.20/0.51      inference('simplify', [status(thm)], ['112'])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.20/0.51          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.20/0.51          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.51               (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | (v2_struct_0 @ X1)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['111', '113'])).
% 0.20/0.51  thf('115', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('117', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('118', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('119', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.20/0.51          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.20/0.51          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | (v2_struct_0 @ X1)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_C_1)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.20/0.51          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51          | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['110', '119'])).
% 0.20/0.51  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('123', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('124', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('125', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('126', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('127', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('128', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_C_1)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.20/0.51          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.51          | (v2_struct_0 @ sk_D_1)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['120', '121', '122', '123', '124', '125', '126', '127'])).
% 0.20/0.51  thf('129', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51        | ~ (m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             sk_D_1 @ sk_F)
% 0.20/0.51        | ~ (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['66', '128'])).
% 0.20/0.51  thf('130', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | ~ (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['53', '129'])).
% 0.20/0.51  thf('131', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51        | ~ (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['130'])).
% 0.20/0.51  thf('132', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '131'])).
% 0.20/0.51  thf('133', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['132'])).
% 0.20/0.51  thf('134', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.20/0.51         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['71'])).
% 0.20/0.51  thf('135', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['72', '107'])).
% 0.20/0.51  thf('136', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 0.20/0.51  thf('137', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['133', '136'])).
% 0.20/0.51  thf(fc2_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('138', plain,
% 0.20/0.51      (![X7 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.20/0.51          | ~ (l1_struct_0 @ X7)
% 0.20/0.51          | (v2_struct_0 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.51  thf('139', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['137', '138'])).
% 0.20/0.51  thf('140', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('141', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('142', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['140', '141'])).
% 0.20/0.51  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('144', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['142', '143'])).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('145', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('146', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['144', '145'])).
% 0.20/0.51  thf('147', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['139', '146'])).
% 0.20/0.51  thf('148', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_D_1)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['147'])).
% 0.20/0.51  thf('149', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('150', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['148', '149'])).
% 0.20/0.51  thf('151', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('152', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['150', '151'])).
% 0.20/0.51  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('154', plain, ((v2_struct_0 @ sk_C_1)),
% 0.20/0.51      inference('clc', [status(thm)], ['152', '153'])).
% 0.20/0.51  thf('155', plain, ($false), inference('demod', [status(thm)], ['0', '154'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
