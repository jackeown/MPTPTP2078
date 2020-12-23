%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gzFCj936hO

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:39 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 368 expanded)
%              Number of leaves         :   40 ( 125 expanded)
%              Depth                    :   19
%              Number of atoms          : 1655 (11263 expanded)
%              Number of equality atoms :   15 ( 273 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t88_tmap_1,conjecture,(
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
                     => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                          = D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                 => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                            = D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                   => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( X21 != k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X21 @ X19 @ X20 ) @ X21 )
      | ( v3_pre_topc @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_connsp_2])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ X20 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ X20 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 )
    | ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 )
    | ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( X21 != k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X21 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_connsp_2])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tmap_1,axiom,(
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
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X30 )
      | ( X30 != X28 )
      | ~ ( r1_tarski @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ X30 @ X27 )
      | ~ ( v3_pre_topc @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ~ ( v3_pre_topc @ X27 @ X24 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( r1_tarski @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X28 )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
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
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('53',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['52','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','51','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) )
    | ~ ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','65'])).

thf('67',plain,
    ( ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('68',plain,(
    m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('69',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('74',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('79',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['71','77','78','79'])).

thf('81',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','80'])).

thf('82',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['82','85'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    r1_tarski @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( X21 != k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X21 @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X19 @ ( sk_D @ X21 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_connsp_2])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( r2_hidden @ X19 @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('93',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( r2_hidden @ X19 @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X19 @ X20 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ sk_F @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('96',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('97',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ sk_F @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r2_hidden @ sk_F @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('100',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('101',plain,
    ( ( r2_hidden @ sk_F @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,(
    r2_hidden @ sk_F @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( v3_pre_topc @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','88','103'])).

thf('105',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','104'])).

thf('106',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gzFCj936hO
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 158 iterations in 0.096s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.35/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.35/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.35/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.35/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.35/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(t88_tmap_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.55             ( l1_pre_topc @ B ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55               ( ![D:$i]:
% 0.38/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.55                   ( ![E:$i]:
% 0.38/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.55                         ( v1_funct_2 @
% 0.38/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                         ( m1_subset_1 @
% 0.38/0.55                           E @ 
% 0.38/0.55                           ( k1_zfmisc_1 @
% 0.38/0.55                             ( k2_zfmisc_1 @
% 0.38/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                       ( ( ( g1_pre_topc @
% 0.38/0.55                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.38/0.55                           ( D ) ) =>
% 0.38/0.55                         ( ![F:$i]:
% 0.38/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.55                             ( ![G:$i]:
% 0.38/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.55                                 ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.55                                     ( r1_tmap_1 @
% 0.38/0.55                                       C @ B @ 
% 0.38/0.55                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.38/0.55                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.55            ( l1_pre_topc @ A ) ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.55                ( l1_pre_topc @ B ) ) =>
% 0.38/0.55              ( ![C:$i]:
% 0.38/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55                  ( ![D:$i]:
% 0.38/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.55                      ( ![E:$i]:
% 0.38/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.55                            ( v1_funct_2 @
% 0.38/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                            ( m1_subset_1 @
% 0.38/0.55                              E @ 
% 0.38/0.55                              ( k1_zfmisc_1 @
% 0.38/0.55                                ( k2_zfmisc_1 @
% 0.38/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                          ( ( ( g1_pre_topc @
% 0.38/0.55                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.38/0.55                              ( D ) ) =>
% 0.38/0.55                            ( ![F:$i]:
% 0.38/0.55                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.55                                ( ![G:$i]:
% 0.38/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.55                                    ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.55                                        ( r1_tmap_1 @
% 0.38/0.55                                          C @ B @ 
% 0.38/0.55                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.38/0.55                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.38/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t28_connsp_2, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( m1_subset_1 @
% 0.38/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.55               ( ~( ( ![D:$i]:
% 0.38/0.55                      ( ( m1_subset_1 @
% 0.38/0.55                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55                        ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.55                          ( ( v3_pre_topc @ D @ A ) & 
% 0.38/0.55                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.38/0.55                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.38/0.55          | ((X21) != (k1_xboole_0))
% 0.38/0.55          | (r2_hidden @ (sk_D @ X21 @ X19 @ X20) @ X21)
% 0.38/0.55          | (v3_pre_topc @ (sk_D @ X21 @ X19 @ X20) @ X20)
% 0.38/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | (v2_struct_0 @ X20))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_connsp_2])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.38/0.55          | (v3_pre_topc @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ X20)
% 0.38/0.55          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ k1_xboole_0)
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.55  thf(t4_subset_1, axiom,
% 0.38/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | (v3_pre_topc @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ X20)
% 0.38/0.55          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ k1_xboole_0)
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.38/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0)
% 0.38/0.55        | (v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '5'])).
% 0.38/0.55  thf('7', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(dt_m1_pre_topc, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X12 : $i, X13 : $i]:
% 0.38/0.55         (~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.55          | (l1_pre_topc @ X12)
% 0.38/0.55          | ~ (l1_pre_topc @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.55  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('11', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(cc1_pre_topc, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]:
% 0.38/0.55         (~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.55          | (v2_pre_topc @ X10)
% 0.38/0.55          | ~ (l1_pre_topc @ X11)
% 0.38/0.55          | ~ (v2_pre_topc @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v2_pre_topc @ sk_D_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.55  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('17', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0)
% 0.38/0.55        | (v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['6', '11', '17'])).
% 0.38/0.55  thf('19', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (((v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0))),
% 0.38/0.55      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf('21', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.38/0.55          | ((X21) != (k1_xboole_0))
% 0.38/0.55          | (m1_subset_1 @ (sk_D @ X21 @ X19 @ X20) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | (v2_struct_0 @ X20))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_connsp_2])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.38/0.55          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.38/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55        | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '25'])).
% 0.38/0.55  thf('27', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('28', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.38/0.55  thf('30', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.55      inference('clc', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('33', plain, (((sk_F) = (sk_G))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)),
% 0.38/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_E @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t84_tmap_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.55             ( l1_pre_topc @ B ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55               ( ![D:$i]:
% 0.38/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.55                   ( ![E:$i]:
% 0.38/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.55                         ( v1_funct_2 @
% 0.38/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                         ( m1_subset_1 @
% 0.38/0.55                           E @ 
% 0.38/0.55                           ( k1_zfmisc_1 @
% 0.38/0.55                             ( k2_zfmisc_1 @
% 0.38/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.55                         ( ![F:$i]:
% 0.38/0.55                           ( ( m1_subset_1 @
% 0.38/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.38/0.55                             ( ![G:$i]:
% 0.38/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.55                                 ( ![H:$i]:
% 0.38/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.55                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.38/0.55                                         ( r2_hidden @ G @ F ) & 
% 0.38/0.55                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.38/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.38/0.55                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.38/0.55                                         ( r1_tmap_1 @
% 0.38/0.55                                           C @ B @ 
% 0.38/0.55                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.38/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 0.38/0.55         X30 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X23)
% 0.38/0.55          | ~ (v2_pre_topc @ X23)
% 0.38/0.55          | ~ (l1_pre_topc @ X23)
% 0.38/0.55          | (v2_struct_0 @ X24)
% 0.38/0.55          | ~ (m1_pre_topc @ X24 @ X25)
% 0.38/0.55          | ~ (m1_pre_topc @ X26 @ X24)
% 0.38/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.38/0.55          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.38/0.55          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.38/0.55               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.38/0.55          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X30)
% 0.38/0.55          | ((X30) != (X28))
% 0.38/0.55          | ~ (r1_tarski @ X27 @ (u1_struct_0 @ X26))
% 0.38/0.55          | ~ (r2_hidden @ X30 @ X27)
% 0.38/0.55          | ~ (v3_pre_topc @ X27 @ X24)
% 0.38/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X24))
% 0.38/0.55          | ~ (m1_subset_1 @ X29 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.38/0.55          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.38/0.55          | ~ (v1_funct_1 @ X29)
% 0.38/0.55          | ~ (m1_pre_topc @ X26 @ X25)
% 0.38/0.55          | (v2_struct_0 @ X26)
% 0.38/0.55          | ~ (l1_pre_topc @ X25)
% 0.38/0.55          | ~ (v2_pre_topc @ X25)
% 0.38/0.55          | (v2_struct_0 @ X25))),
% 0.38/0.55      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X25)
% 0.38/0.55          | ~ (v2_pre_topc @ X25)
% 0.38/0.55          | ~ (l1_pre_topc @ X25)
% 0.38/0.55          | (v2_struct_0 @ X26)
% 0.38/0.55          | ~ (m1_pre_topc @ X26 @ X25)
% 0.38/0.55          | ~ (v1_funct_1 @ X29)
% 0.38/0.55          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.38/0.55          | ~ (m1_subset_1 @ X29 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.38/0.55          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 0.38/0.55          | ~ (v3_pre_topc @ X27 @ X24)
% 0.38/0.55          | ~ (r2_hidden @ X28 @ X27)
% 0.38/0.55          | ~ (r1_tarski @ X27 @ (u1_struct_0 @ X26))
% 0.38/0.55          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X28)
% 0.38/0.55          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.38/0.55               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.38/0.55          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.38/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.38/0.55          | ~ (m1_pre_topc @ X26 @ X24)
% 0.38/0.55          | ~ (m1_pre_topc @ X24 @ X25)
% 0.38/0.55          | (v2_struct_0 @ X24)
% 0.38/0.55          | ~ (l1_pre_topc @ X23)
% 0.38/0.55          | ~ (v2_pre_topc @ X23)
% 0.38/0.55          | (v2_struct_0 @ X23))),
% 0.38/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_B)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ sk_D_1)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.38/0.55          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.38/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.55          | ~ (v3_pre_topc @ X2 @ sk_D_1)
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.55               (u1_struct_0 @ sk_B))
% 0.38/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.55          | (v2_struct_0 @ X1)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['35', '37'])).
% 0.38/0.55  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ sk_D_1)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.38/0.55          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.38/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.55          | ~ (v3_pre_topc @ X2 @ sk_D_1)
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.55          | (v2_struct_0 @ X1)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.38/0.55          | ~ (v3_pre_topc @ X0 @ sk_D_1)
% 0.38/0.55          | ~ (r2_hidden @ sk_F @ X0)
% 0.38/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.38/0.55          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_D_1)
% 0.38/0.55          | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['34', '43'])).
% 0.38/0.55  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('48', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('49', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('50', plain, (((sk_F) = (sk_G))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('51', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t2_tsep_1, axiom,
% 0.38/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.38/0.55  thf(t65_pre_topc, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( l1_pre_topc @ B ) =>
% 0.38/0.55           ( ( m1_pre_topc @ A @ B ) <=>
% 0.38/0.55             ( m1_pre_topc @
% 0.38/0.55               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         (~ (l1_pre_topc @ X17)
% 0.38/0.55          | ~ (m1_pre_topc @ X18 @ X17)
% 0.38/0.55          | (m1_pre_topc @ X18 @ 
% 0.38/0.55             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.38/0.55          | ~ (l1_pre_topc @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (m1_pre_topc @ X0 @ 
% 0.38/0.55             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.55          | ~ (l1_pre_topc @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((m1_pre_topc @ X0 @ 
% 0.38/0.55           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.55          | ~ (l1_pre_topc @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.55  thf('57', plain, (((m1_pre_topc @ sk_C @ sk_D_1) | ~ (l1_pre_topc @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['52', '56'])).
% 0.38/0.55  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      (![X12 : $i, X13 : $i]:
% 0.38/0.55         (~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.55          | (l1_pre_topc @ X12)
% 0.38/0.55          | ~ (l1_pre_topc @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.55  thf('60', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.55  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['57', '62'])).
% 0.38/0.55  thf('64', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ~ (v3_pre_topc @ X0 @ sk_D_1)
% 0.38/0.55          | ~ (r2_hidden @ sk_F @ X0)
% 0.38/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.38/0.55          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55          | (v2_struct_0 @ sk_D_1)
% 0.38/0.55          | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['44', '45', '46', '47', '48', '51', '63', '64'])).
% 0.38/0.55  thf('66', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1)
% 0.38/0.55        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55        | ~ (r1_tarski @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55             (u1_struct_0 @ sk_C))
% 0.38/0.55        | ~ (r2_hidden @ sk_F @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1))
% 0.38/0.55        | ~ (v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '65'])).
% 0.38/0.55  thf('67', plain,
% 0.38/0.55      (((v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0))),
% 0.38/0.55      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf('68', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.55      inference('clc', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('69', plain,
% 0.38/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t60_pre_topc, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.38/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.38/0.55           ( ( v3_pre_topc @
% 0.38/0.55               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.38/0.55             ( m1_subset_1 @
% 0.38/0.55               B @ 
% 0.38/0.55               ( k1_zfmisc_1 @
% 0.38/0.55                 ( u1_struct_0 @
% 0.38/0.55                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('70', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         (~ (v3_pre_topc @ X14 @ 
% 0.38/0.55             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.38/0.55          | ~ (m1_subset_1 @ X14 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (u1_struct_0 @ 
% 0.38/0.55                 (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))))
% 0.38/0.55          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.55          | ~ (l1_pre_topc @ X15)
% 0.38/0.55          | ~ (v2_pre_topc @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.38/0.55  thf('71', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55          | ~ (v2_pre_topc @ sk_C)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_C)
% 0.38/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.38/0.55          | ~ (v3_pre_topc @ X0 @ 
% 0.38/0.55               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.55  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('73', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i]:
% 0.38/0.55         (~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.55          | (v2_pre_topc @ X10)
% 0.38/0.55          | ~ (l1_pre_topc @ X11)
% 0.38/0.55          | ~ (v2_pre_topc @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.55  thf('74', plain,
% 0.38/0.55      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.55  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('77', plain, ((v2_pre_topc @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.38/0.55  thf('78', plain, ((l1_pre_topc @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.55  thf('79', plain,
% 0.38/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('80', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.38/0.55          | ~ (v3_pre_topc @ X0 @ sk_D_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['71', '77', '78', '79'])).
% 0.38/0.55  thf('81', plain,
% 0.38/0.55      ((~ (v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['68', '80'])).
% 0.38/0.55  thf('82', plain,
% 0.38/0.55      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0)
% 0.38/0.55        | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['67', '81'])).
% 0.38/0.55  thf('83', plain,
% 0.38/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf(t4_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.55  thf('84', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X5 @ X6)
% 0.38/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.38/0.55          | (m1_subset_1 @ X5 @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.55  thf('85', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.55  thf('86', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.38/0.55      inference('clc', [status(thm)], ['82', '85'])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('87', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i]:
% 0.38/0.55         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('88', plain,
% 0.38/0.55      ((r1_tarski @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ (u1_struct_0 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.38/0.55  thf('89', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('90', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.38/0.55          | ((X21) != (k1_xboole_0))
% 0.38/0.55          | (r2_hidden @ (sk_D @ X21 @ X19 @ X20) @ X21)
% 0.38/0.55          | (r2_hidden @ X19 @ (sk_D @ X21 @ X19 @ X20))
% 0.38/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | (v2_struct_0 @ X20))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_connsp_2])).
% 0.38/0.55  thf('91', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.38/0.55          | (r2_hidden @ X19 @ (sk_D @ k1_xboole_0 @ X19 @ X20))
% 0.38/0.55          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ k1_xboole_0)
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['90'])).
% 0.38/0.55  thf('92', plain,
% 0.38/0.55      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf('93', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | (r2_hidden @ X19 @ (sk_D @ k1_xboole_0 @ X19 @ X20))
% 0.38/0.55          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X19 @ X20) @ k1_xboole_0)
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20)))),
% 0.38/0.55      inference('demod', [status(thm)], ['91', '92'])).
% 0.38/0.55  thf('94', plain,
% 0.38/0.55      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0)
% 0.38/0.55        | (r2_hidden @ sk_F @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1))
% 0.38/0.55        | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['89', '93'])).
% 0.38/0.55  thf('95', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('96', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.55  thf('97', plain,
% 0.38/0.55      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0)
% 0.38/0.55        | (r2_hidden @ sk_F @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1))
% 0.38/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.38/0.55  thf('98', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('99', plain,
% 0.38/0.55      (((r2_hidden @ sk_F @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1))
% 0.38/0.55        | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0))),
% 0.38/0.55      inference('clc', [status(thm)], ['97', '98'])).
% 0.38/0.55  thf(t7_ordinal1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.55  thf('100', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('101', plain,
% 0.38/0.55      (((r2_hidden @ sk_F @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1))
% 0.38/0.55        | ~ (r1_tarski @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.55  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('103', plain,
% 0.38/0.55      ((r2_hidden @ sk_F @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['101', '102'])).
% 0.38/0.55  thf('104', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1)
% 0.38/0.55        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55        | ~ (v3_pre_topc @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['66', '88', '103'])).
% 0.38/0.55  thf('105', plain,
% 0.38/0.55      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1) @ k1_xboole_0)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['20', '104'])).
% 0.38/0.55  thf('106', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('107', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1)
% 0.38/0.55        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | ~ (r1_tarski @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ sk_F @ sk_D_1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['105', '106'])).
% 0.38/0.55  thf('108', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('109', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1)
% 0.38/0.55        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['107', '108'])).
% 0.38/0.55  thf('110', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('111', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v2_struct_0 @ sk_D_1)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.55  thf('112', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('113', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.38/0.55  thf('114', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('115', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.38/0.55      inference('clc', [status(thm)], ['113', '114'])).
% 0.38/0.55  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('117', plain, ((v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('clc', [status(thm)], ['115', '116'])).
% 0.38/0.55  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
