%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wf6fGhm5D4

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:22 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 647 expanded)
%              Number of leaves         :   38 ( 197 expanded)
%              Depth                    :   32
%              Number of atoms          : 2423 (22389 expanded)
%              Number of equality atoms :   11 ( 283 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

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

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r1_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( X15
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v1_tsep_1 @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v3_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X13 ) @ X14 )
      | ~ ( v1_tsep_1 @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( m1_connsp_2 @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 @ X11 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('76',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['68'])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ~ ( r1_tmap_1 @ X25 @ X21 @ X26 @ X24 )
      | ( X24 != X27 )
      | ( r1_tmap_1 @ X22 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X26 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X22 ) )
      | ( r1_tmap_1 @ X22 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X26 ) @ X27 )
      | ~ ( r1_tmap_1 @ X25 @ X21 @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
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
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
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
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
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
    inference('sup-',[status(thm)],['75','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
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
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['74','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['72'])).

thf('98',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['68'])).

thf('110',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['73','108','109'])).

thf('111',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['71','110'])).

thf('112',plain,(
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

thf('113',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X35 )
      | ( X35 != X33 )
      | ~ ( m1_connsp_2 @ X32 @ X29 @ X35 )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('114',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_connsp_2 @ X32 @ X29 @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
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
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
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
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
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
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('127',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ sk_D_1 @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','129'])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ sk_F @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['72'])).

thf('136',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['73','108'])).

thf('137',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('139',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('143',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['143','144'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('146',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('147',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['140','147'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    $false ),
    inference(demod,[status(thm)],['0','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wf6fGhm5D4
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 186 iterations in 0.110s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.57  thf(t86_tmap_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.57             ( l1_pre_topc @ B ) ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.57               ( ![D:$i]:
% 0.38/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.57                   ( ![E:$i]:
% 0.38/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.57                         ( v1_funct_2 @
% 0.38/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.57                         ( m1_subset_1 @
% 0.38/0.57                           E @ 
% 0.38/0.57                           ( k1_zfmisc_1 @
% 0.38/0.57                             ( k2_zfmisc_1 @
% 0.38/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.57                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.38/0.57                         ( ![F:$i]:
% 0.38/0.57                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.57                             ( ![G:$i]:
% 0.38/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.57                                 ( ( ( F ) = ( G ) ) =>
% 0.38/0.57                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.38/0.57                                     ( r1_tmap_1 @
% 0.38/0.57                                       C @ B @ 
% 0.38/0.57                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.57            ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.57                ( l1_pre_topc @ B ) ) =>
% 0.38/0.57              ( ![C:$i]:
% 0.38/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.57                  ( ![D:$i]:
% 0.38/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.57                      ( ![E:$i]:
% 0.38/0.57                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.57                            ( v1_funct_2 @
% 0.38/0.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.57                            ( m1_subset_1 @
% 0.38/0.57                              E @ 
% 0.38/0.57                              ( k1_zfmisc_1 @
% 0.38/0.57                                ( k2_zfmisc_1 @
% 0.38/0.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.57                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.38/0.57                            ( ![F:$i]:
% 0.38/0.57                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.57                                ( ![G:$i]:
% 0.38/0.57                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.57                                    ( ( ( F ) = ( G ) ) =>
% 0.38/0.57                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.38/0.57                                        ( r1_tmap_1 @
% 0.38/0.57                                          C @ B @ 
% 0.38/0.57                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.38/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('2', plain, (((sk_F) = (sk_G))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(d2_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X0 @ X1)
% 0.38/0.57          | (r2_hidden @ X0 @ X1)
% 0.38/0.57          | (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.57        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.57  thf('6', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t1_tsep_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.57           ( m1_subset_1 @
% 0.38/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X16 @ X17)
% 0.38/0.57          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.57          | ~ (l1_pre_topc @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_D_1)
% 0.38/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_m1_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.57  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('14', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.38/0.57  thf(t9_connsp_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.38/0.57             ( ![C:$i]:
% 0.38/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.57                      ( ![D:$i]:
% 0.38/0.57                        ( ( m1_subset_1 @
% 0.38/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.38/0.57                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.57          | ~ (v3_pre_topc @ X9 @ X10)
% 0.38/0.57          | (r1_tarski @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.38/0.57          | ~ (r2_hidden @ X11 @ X9)
% 0.38/0.57          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.38/0.57          | ~ (l1_pre_topc @ X10)
% 0.38/0.57          | ~ (v2_pre_topc @ X10)
% 0.38/0.57          | (v2_struct_0 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ sk_D_1)
% 0.38/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.57          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.57             (u1_struct_0 @ sk_C_1))
% 0.38/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('18', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc1_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X3 @ X4)
% 0.38/0.57          | (v2_pre_topc @ X3)
% 0.38/0.57          | ~ (l1_pre_topc @ X4)
% 0.38/0.57          | ~ (v2_pre_topc @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v2_pre_topc @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.57  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('23', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.38/0.57  thf('24', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ sk_D_1)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.57          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.57             (u1_struct_0 @ sk_C_1))
% 0.38/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '14'])).
% 0.38/0.57  thf(t16_tsep_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.57                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.38/0.57                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X13 @ X14)
% 0.38/0.57          | ((X15) != (u1_struct_0 @ X13))
% 0.38/0.57          | ~ (v1_tsep_1 @ X13 @ X14)
% 0.38/0.57          | ~ (m1_pre_topc @ X13 @ X14)
% 0.38/0.57          | (v3_pre_topc @ X15 @ X14)
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.57          | ~ (l1_pre_topc @ X14)
% 0.38/0.57          | ~ (v2_pre_topc @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i]:
% 0.38/0.57         (~ (v2_pre_topc @ X14)
% 0.38/0.57          | ~ (l1_pre_topc @ X14)
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.57          | (v3_pre_topc @ (u1_struct_0 @ X13) @ X14)
% 0.38/0.57          | ~ (v1_tsep_1 @ X13 @ X14)
% 0.38/0.57          | ~ (m1_pre_topc @ X13 @ X14))),
% 0.38/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      ((~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.38/0.57        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.38/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.57        | ~ (v2_pre_topc @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '28'])).
% 0.38/0.57  thf('30', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('32', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('33', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.38/0.58  thf('34', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['25', '34'])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (((r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '35'])).
% 0.38/0.58  thf('37', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58           (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58           (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.58  thf('41', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '14'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.58          | ~ (v3_pre_topc @ X9 @ X10)
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ X11 @ X9 @ X10) @ X10 @ X11)
% 0.38/0.58          | ~ (r2_hidden @ X11 @ X9)
% 0.38/0.58          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.38/0.58          | ~ (l1_pre_topc @ X10)
% 0.38/0.58          | ~ (v2_pre_topc @ X10)
% 0.38/0.58          | (v2_struct_0 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             sk_D_1 @ X0)
% 0.38/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.58  thf('45', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.38/0.58  thf('46', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             sk_D_1 @ X0)
% 0.38/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.58  thf('48', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             sk_D_1 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (((m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58         sk_D_1 @ sk_F)
% 0.38/0.58        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '49'])).
% 0.38/0.58  thf('51', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58           sk_D_1 @ sk_F))),
% 0.38/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58           sk_D_1 @ sk_F))),
% 0.38/0.58      inference('sup-', [status(thm)], ['40', '52'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '14'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.58          | ~ (v3_pre_topc @ X9 @ X10)
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.58          | ~ (r2_hidden @ X11 @ X9)
% 0.38/0.58          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.38/0.58          | ~ (l1_pre_topc @ X10)
% 0.38/0.58          | ~ (v2_pre_topc @ X10)
% 0.38/0.58          | (v2_struct_0 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.58  thf('58', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.38/0.58  thf('59', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.38/0.58  thf('61', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (m1_subset_1 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['54', '62'])).
% 0.38/0.58  thf('64', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (m1_subset_1 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.58  thf('66', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (((m1_subset_1 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['65', '66'])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)
% 0.38/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.58      inference('split', [status(esa)], ['68'])).
% 0.38/0.58  thf('70', plain, (((sk_F) = (sk_G))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.58      inference('demod', [status(thm)], ['69', '70'])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)
% 0.38/0.58        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)) | 
% 0.38/0.58       ~
% 0.38/0.58       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))),
% 0.38/0.58      inference('split', [status(esa)], ['72'])).
% 0.38/0.58  thf('74', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('75', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('split', [status(esa)], ['68'])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t81_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                         ( v1_funct_2 @
% 0.38/0.58                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                         ( m1_subset_1 @
% 0.38/0.58                           E @ 
% 0.38/0.58                           ( k1_zfmisc_1 @
% 0.38/0.58                             ( k2_zfmisc_1 @
% 0.38/0.58                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                       ( ![F:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.58                           ( ![G:$i]:
% 0.38/0.58                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.58                               ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.58                                   ( m1_pre_topc @ D @ C ) & 
% 0.38/0.58                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.38/0.58                                 ( r1_tmap_1 @
% 0.38/0.58                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.38/0.58                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('78', plain,
% 0.38/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X21)
% 0.38/0.58          | ~ (v2_pre_topc @ X21)
% 0.38/0.58          | ~ (l1_pre_topc @ X21)
% 0.38/0.58          | (v2_struct_0 @ X22)
% 0.38/0.58          | ~ (m1_pre_topc @ X22 @ X23)
% 0.38/0.58          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.38/0.58          | ~ (m1_pre_topc @ X22 @ X25)
% 0.38/0.58          | ~ (r1_tmap_1 @ X25 @ X21 @ X26 @ X24)
% 0.38/0.58          | ((X24) != (X27))
% 0.38/0.58          | (r1_tmap_1 @ X22 @ X21 @ 
% 0.38/0.58             (k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X26) @ X27)
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X22))
% 0.38/0.58          | ~ (m1_subset_1 @ X26 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))))
% 0.38/0.58          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))
% 0.38/0.58          | ~ (v1_funct_1 @ X26)
% 0.38/0.58          | ~ (m1_pre_topc @ X25 @ X23)
% 0.38/0.58          | (v2_struct_0 @ X25)
% 0.38/0.58          | ~ (l1_pre_topc @ X23)
% 0.38/0.58          | ~ (v2_pre_topc @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23))),
% 0.38/0.58      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X23)
% 0.38/0.58          | ~ (v2_pre_topc @ X23)
% 0.38/0.58          | ~ (l1_pre_topc @ X23)
% 0.38/0.58          | (v2_struct_0 @ X25)
% 0.38/0.58          | ~ (m1_pre_topc @ X25 @ X23)
% 0.38/0.58          | ~ (v1_funct_1 @ X26)
% 0.38/0.58          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))
% 0.38/0.58          | ~ (m1_subset_1 @ X26 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))))
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X22))
% 0.38/0.58          | (r1_tmap_1 @ X22 @ X21 @ 
% 0.38/0.58             (k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X26) @ X27)
% 0.38/0.58          | ~ (r1_tmap_1 @ X25 @ X21 @ X26 @ X27)
% 0.38/0.58          | ~ (m1_pre_topc @ X22 @ X25)
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.38/0.58          | ~ (m1_pre_topc @ X22 @ X23)
% 0.38/0.58          | (v2_struct_0 @ X22)
% 0.38/0.58          | ~ (l1_pre_topc @ X21)
% 0.38/0.58          | ~ (v2_pre_topc @ X21)
% 0.38/0.58          | (v2_struct_0 @ X21))),
% 0.38/0.58      inference('simplify', [status(thm)], ['78'])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.38/0.58          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.38/0.58          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.38/0.58             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | ~ (v2_pre_topc @ X1)
% 0.38/0.58          | (v2_struct_0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['77', '79'])).
% 0.38/0.58  thf('81', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.38/0.58          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.38/0.58          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.38/0.58             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | ~ (v2_pre_topc @ X1)
% 0.38/0.58          | (v2_struct_0 @ X1))),
% 0.38/0.58      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      ((![X0 : $i, X1 : $i]:
% 0.38/0.58          ((v2_struct_0 @ X0)
% 0.38/0.58           | ~ (v2_pre_topc @ X0)
% 0.38/0.58           | ~ (l1_pre_topc @ X0)
% 0.38/0.58           | (v2_struct_0 @ sk_D_1)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.58           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.38/0.58           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.38/0.58           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.38/0.58           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58           | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.58           | (v2_struct_0 @ X1)
% 0.38/0.58           | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['76', '85'])).
% 0.38/0.58  thf('87', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('88', plain,
% 0.38/0.58      ((![X0 : $i, X1 : $i]:
% 0.38/0.58          ((v2_struct_0 @ X0)
% 0.38/0.58           | ~ (v2_pre_topc @ X0)
% 0.38/0.58           | ~ (l1_pre_topc @ X0)
% 0.38/0.58           | (v2_struct_0 @ sk_D_1)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.58           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.38/0.58           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.38/0.58           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.38/0.58           | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.58           | (v2_struct_0 @ X1)
% 0.38/0.58           | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.58  thf('89', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          ((v2_struct_0 @ sk_B)
% 0.38/0.58           | (v2_struct_0 @ sk_C_1)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.38/0.58           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.58           | (v2_struct_0 @ sk_D_1)
% 0.38/0.58           | ~ (l1_pre_topc @ X0)
% 0.38/0.58           | ~ (v2_pre_topc @ X0)
% 0.38/0.58           | (v2_struct_0 @ X0)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['75', '88'])).
% 0.38/0.58  thf('90', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          ((v2_struct_0 @ sk_B)
% 0.38/0.58           | (v2_struct_0 @ sk_C_1)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.38/0.58           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.58           | (v2_struct_0 @ sk_D_1)
% 0.38/0.58           | ~ (l1_pre_topc @ X0)
% 0.38/0.58           | ~ (v2_pre_topc @ X0)
% 0.38/0.58           | (v2_struct_0 @ X0)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.38/0.58  thf('92', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A)
% 0.38/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58         | (v2_struct_0 @ sk_D_1)
% 0.38/0.58         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.38/0.58         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.58         | (v2_struct_0 @ sk_C_1)
% 0.38/0.58         | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['74', '91'])).
% 0.38/0.58  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('95', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A)
% 0.38/0.58         | (v2_struct_0 @ sk_D_1)
% 0.38/0.58         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)
% 0.38/0.58         | (v2_struct_0 @ sk_C_1)
% 0.38/0.58         | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.38/0.58  thf('97', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.58      inference('split', [status(esa)], ['72'])).
% 0.38/0.58  thf('98', plain, (((sk_F) = (sk_G))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('99', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.38/0.58      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_B)
% 0.38/0.58         | (v2_struct_0 @ sk_C_1)
% 0.38/0.58         | (v2_struct_0 @ sk_D_1)
% 0.38/0.58         | (v2_struct_0 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['96', '99'])).
% 0.38/0.58  thf('101', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('102', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['100', '101'])).
% 0.38/0.58  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.38/0.58  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C_1))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('clc', [status(thm)], ['104', '105'])).
% 0.38/0.58  thf('107', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('108', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.38/0.58       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.38/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.38/0.58  thf('109', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.38/0.58       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.38/0.58      inference('split', [status(esa)], ['68'])).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_G))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['73', '108', '109'])).
% 0.38/0.58  thf('111', plain,
% 0.38/0.58      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.58        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_F)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['71', '110'])).
% 0.38/0.58  thf('112', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t83_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                         ( v1_funct_2 @
% 0.38/0.58                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                         ( m1_subset_1 @
% 0.38/0.58                           E @ 
% 0.38/0.58                           ( k1_zfmisc_1 @
% 0.38/0.58                             ( k2_zfmisc_1 @
% 0.38/0.58                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                       ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.58                         ( ![F:$i]:
% 0.38/0.58                           ( ( m1_subset_1 @
% 0.38/0.58                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.38/0.58                             ( ![G:$i]:
% 0.38/0.58                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.58                                 ( ![H:$i]:
% 0.38/0.58                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.58                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.38/0.58                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.38/0.58                                         ( ( G ) = ( H ) ) ) =>
% 0.38/0.58                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.38/0.58                                         ( r1_tmap_1 @
% 0.38/0.58                                           C @ B @ 
% 0.38/0.58                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.38/0.58                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('113', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.38/0.58         X35 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X28)
% 0.38/0.58          | ~ (v2_pre_topc @ X28)
% 0.38/0.58          | ~ (l1_pre_topc @ X28)
% 0.38/0.58          | (v2_struct_0 @ X29)
% 0.38/0.58          | ~ (m1_pre_topc @ X29 @ X30)
% 0.38/0.58          | ~ (m1_pre_topc @ X31 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.58          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.38/0.58          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.38/0.58               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.38/0.58          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X35)
% 0.38/0.58          | ((X35) != (X33))
% 0.38/0.58          | ~ (m1_connsp_2 @ X32 @ X29 @ X35)
% 0.38/0.58          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X31))
% 0.38/0.58          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X29))
% 0.38/0.58          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.38/0.58          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.38/0.58          | ~ (v1_funct_1 @ X34)
% 0.38/0.58          | ~ (m1_pre_topc @ X31 @ X30)
% 0.38/0.58          | (v2_struct_0 @ X31)
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.38/0.58  thf('114', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X31)
% 0.38/0.58          | ~ (m1_pre_topc @ X31 @ X30)
% 0.38/0.58          | ~ (v1_funct_1 @ X34)
% 0.38/0.58          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.38/0.58          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.38/0.58          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 0.38/0.58          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X31))
% 0.38/0.58          | ~ (m1_connsp_2 @ X32 @ X29 @ X33)
% 0.38/0.58          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X33)
% 0.38/0.58          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.38/0.58               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.38/0.58          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.38/0.58          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.58          | ~ (m1_pre_topc @ X31 @ X29)
% 0.38/0.58          | ~ (m1_pre_topc @ X29 @ X30)
% 0.38/0.58          | (v2_struct_0 @ X29)
% 0.38/0.58          | ~ (l1_pre_topc @ X28)
% 0.38/0.58          | ~ (v2_pre_topc @ X28)
% 0.38/0.58          | (v2_struct_0 @ X28))),
% 0.38/0.58      inference('simplify', [status(thm)], ['113'])).
% 0.38/0.58  thf('115', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.58          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.38/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.38/0.58          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.38/0.58          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['112', '114'])).
% 0.38/0.58  thf('116', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('118', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('119', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('120', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.58          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.58               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.38/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.38/0.58          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.38/0.58          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.38/0.58  thf('121', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_C_1)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.38/0.58          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.38/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['111', '120'])).
% 0.38/0.58  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('124', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('125', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('126', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('127', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('128', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('129', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_C_1)
% 0.38/0.58          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.38/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['121', '122', '123', '124', '125', '126', '127', '128'])).
% 0.38/0.58  thf('130', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58        | ~ (m1_connsp_2 @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             sk_D_1 @ sk_F)
% 0.38/0.58        | ~ (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['67', '129'])).
% 0.38/0.58  thf('131', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | ~ (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['53', '130'])).
% 0.38/0.58  thf('132', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58        | ~ (r1_tarski @ (sk_D @ sk_F @ (u1_struct_0 @ sk_C_1) @ sk_D_1) @ 
% 0.38/0.58             (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['131'])).
% 0.38/0.58  thf('133', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '132'])).
% 0.38/0.58  thf('134', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['133'])).
% 0.38/0.58  thf('135', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.38/0.58         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.38/0.58      inference('split', [status(esa)], ['72'])).
% 0.38/0.58  thf('136', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['73', '108'])).
% 0.38/0.58  thf('137', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['135', '136'])).
% 0.38/0.58  thf('138', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['134', '137'])).
% 0.38/0.58  thf(fc2_struct_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.58  thf('139', plain,
% 0.38/0.58      (![X8 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.38/0.58          | ~ (l1_struct_0 @ X8)
% 0.38/0.58          | (v2_struct_0 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.58  thf('140', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | ~ (l1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['138', '139'])).
% 0.38/0.58  thf('141', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('142', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.58  thf('143', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['141', '142'])).
% 0.38/0.58  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('145', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['143', '144'])).
% 0.38/0.58  thf(dt_l1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.58  thf('146', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('147', plain, ((l1_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('sup-', [status(thm)], ['145', '146'])).
% 0.38/0.58  thf('148', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['140', '147'])).
% 0.38/0.58  thf('149', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('simplify', [status(thm)], ['148'])).
% 0.38/0.58  thf('150', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('151', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['149', '150'])).
% 0.38/0.58  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('153', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('clc', [status(thm)], ['151', '152'])).
% 0.38/0.58  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('155', plain, ((v2_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('clc', [status(thm)], ['153', '154'])).
% 0.38/0.58  thf('156', plain, ($false), inference('demod', [status(thm)], ['0', '155'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
