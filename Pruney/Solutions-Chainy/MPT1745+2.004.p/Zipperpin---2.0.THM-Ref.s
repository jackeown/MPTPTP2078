%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dFOnkKc2gk

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 183 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   22
%              Number of atoms          : 1343 (7241 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t54_tmap_1,conjecture,(
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
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ( ( ( r1_tmap_1 @ C @ A @ D @ F )
                              & ( v5_pre_topc @ E @ A @ B ) )
                           => ( r1_tmap_1 @ C @ B @ ( k1_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ F ) ) ) ) ) ) ) ) )).

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
                  & ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                           => ( ( ( r1_tmap_1 @ C @ A @ D @ F )
                                & ( v5_pre_topc @ E @ A @ B ) )
                             => ( r1_tmap_1 @ C @ B @ ( k1_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ F ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ X7 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X7 @ X8 @ X6 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tmap_1,axiom,(
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
             => ( ( v5_pre_topc @ C @ B @ A )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v5_pre_topc @ X12 @ X11 @ X13 )
      | ( r1_tmap_1 @ X11 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ sk_E @ sk_A @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_pre_topc @ sk_E @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18','19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_tmap_1,axiom,(
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
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                             => ( ( ( G
                                    = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ D @ F ) )
                                  & ( r1_tmap_1 @ B @ C @ D @ F )
                                  & ( r1_tmap_1 @ C @ A @ E @ G ) )
                               => ( r1_tmap_1 @ B @ A @ ( k1_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ E ) @ F ) ) ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X17 @ X16 @ X18 )
      | ( r1_tmap_1 @ X15 @ X19 @ ( k1_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) @ X16 @ X20 ) @ X18 )
      | ( X21
       != ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) )
      | ~ ( r1_tmap_1 @ X17 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_tmap_1 @ X17 @ X19 @ X20 @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) )
      | ( r1_tmap_1 @ X15 @ X19 @ ( k1_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) @ X16 @ X20 ) @ X18 )
      | ~ ( r1_tmap_1 @ X15 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B_2 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_D_1 @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','55'])).

thf('57',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dFOnkKc2gk
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 53 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(t54_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.50                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.50                     ( v1_funct_2 @
% 0.20/0.50                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                     ( m1_subset_1 @
% 0.20/0.50                       D @ 
% 0.20/0.50                       ( k1_zfmisc_1 @
% 0.20/0.50                         ( k2_zfmisc_1 @
% 0.20/0.50                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                           ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.20/0.50                               ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.20/0.50                             ( r1_tmap_1 @
% 0.20/0.50                               C @ B @ 
% 0.20/0.50                               ( k1_partfun1 @
% 0.20/0.50                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.50                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.50                                 D @ E ) @ 
% 0.20/0.50                               F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50                ( l1_pre_topc @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.50                    ( l1_pre_topc @ C ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.50                        ( v1_funct_2 @
% 0.20/0.50                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                        ( m1_subset_1 @
% 0.20/0.50                          D @ 
% 0.20/0.50                          ( k1_zfmisc_1 @
% 0.20/0.50                            ( k2_zfmisc_1 @
% 0.20/0.50                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                      ( ![E:$i]:
% 0.20/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                            ( v1_funct_2 @
% 0.20/0.50                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                            ( m1_subset_1 @
% 0.20/0.50                              E @ 
% 0.20/0.50                              ( k1_zfmisc_1 @
% 0.20/0.50                                ( k2_zfmisc_1 @
% 0.20/0.50                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                          ( ![F:$i]:
% 0.20/0.50                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                              ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.20/0.50                                  ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.20/0.50                                ( r1_tmap_1 @
% 0.20/0.50                                  C @ B @ 
% 0.20/0.50                                  ( k1_partfun1 @
% 0.20/0.50                                    ( u1_struct_0 @ C ) @ 
% 0.20/0.50                                    ( u1_struct_0 @ A ) @ 
% 0.20/0.50                                    ( u1_struct_0 @ A ) @ 
% 0.20/0.50                                    ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.20/0.50                                  F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t54_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('2', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k3_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.50         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.20/0.50          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 0.20/0.50          | ~ (v1_funct_1 @ X6)
% 0.20/0.50          | (v1_xboole_0 @ X7)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ X7)
% 0.20/0.50          | (m1_subset_1 @ (k3_funct_2 @ X7 @ X8 @ X6 @ X9) @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ 
% 0.20/0.50           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            sk_D_1 @ X0) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.50          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ 
% 0.20/0.50           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            sk_D_1 @ X0) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (m1_subset_1 @ 
% 0.20/0.50           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            sk_D_1 @ sk_F) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (m1_subset_1 @ 
% 0.20/0.50           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            sk_D_1 @ sk_F) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t49_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.20/0.50                 ( ![D:$i]:
% 0.20/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X11)
% 0.20/0.50          | ~ (v2_pre_topc @ X11)
% 0.20/0.50          | ~ (l1_pre_topc @ X11)
% 0.20/0.50          | ~ (v5_pre_topc @ X12 @ X11 @ X13)
% 0.20/0.50          | (r1_tmap_1 @ X11 @ X13 @ X12 @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))))
% 0.20/0.50          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (v1_funct_1 @ X12)
% 0.20/0.50          | ~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13)
% 0.20/0.50          | (v2_struct_0 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B_2)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B_2)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B_2)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               (u1_struct_0 @ sk_B_2))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ X0)
% 0.20/0.50          | ~ (v5_pre_topc @ sk_E @ sk_A @ sk_B_2)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((v2_pre_topc @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((l1_pre_topc @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain, ((v5_pre_topc @ sk_E @ sk_A @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B_2)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['13', '14', '15', '16', '17', '18', '19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ 
% 0.20/0.50           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            sk_D_1 @ sk_F))
% 0.20/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t52_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.50                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.50                     ( v1_funct_2 @
% 0.20/0.50                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.50                     ( m1_subset_1 @
% 0.20/0.50                       D @ 
% 0.20/0.50                       ( k1_zfmisc_1 @
% 0.20/0.50                         ( k2_zfmisc_1 @
% 0.20/0.50                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                           ( ![G:$i]:
% 0.20/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                               ( ( ( ( G ) =
% 0.20/0.50                                     ( k3_funct_2 @
% 0.20/0.50                                       ( u1_struct_0 @ B ) @ 
% 0.20/0.50                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.20/0.50                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.20/0.50                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.20/0.50                                 ( r1_tmap_1 @
% 0.20/0.50                                   B @ A @ 
% 0.20/0.50                                   ( k1_partfun1 @
% 0.20/0.50                                     ( u1_struct_0 @ B ) @ 
% 0.20/0.50                                     ( u1_struct_0 @ C ) @ 
% 0.20/0.50                                     ( u1_struct_0 @ C ) @ 
% 0.20/0.50                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.20/0.50                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X15)
% 0.20/0.50          | ~ (v2_pre_topc @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X15)
% 0.20/0.50          | ~ (v1_funct_1 @ X16)
% 0.20/0.50          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (r1_tmap_1 @ X15 @ X17 @ X16 @ X18)
% 0.20/0.50          | (r1_tmap_1 @ X15 @ X19 @ 
% 0.20/0.50             (k1_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.20/0.50              (u1_struct_0 @ X17) @ (u1_struct_0 @ X19) @ X16 @ X20) @ 
% 0.20/0.50             X18)
% 0.20/0.50          | ((X21)
% 0.20/0.50              != (k3_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.20/0.50                  X16 @ X18))
% 0.20/0.50          | ~ (r1_tmap_1 @ X17 @ X19 @ X20 @ X21)
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))))
% 0.20/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (l1_pre_topc @ X17)
% 0.20/0.50          | ~ (v2_pre_topc @ X17)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | ~ (l1_pre_topc @ X19)
% 0.20/0.50          | ~ (v2_pre_topc @ X19)
% 0.20/0.50          | (v2_struct_0 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X19)
% 0.20/0.50          | ~ (v2_pre_topc @ X19)
% 0.20/0.50          | ~ (l1_pre_topc @ X19)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | ~ (v2_pre_topc @ X17)
% 0.20/0.50          | ~ (l1_pre_topc @ X17)
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))))
% 0.20/0.50          | ~ (m1_subset_1 @ 
% 0.20/0.50               (k3_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ X16 @ 
% 0.20/0.50                X18) @ 
% 0.20/0.50               (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (r1_tmap_1 @ X17 @ X19 @ X20 @ 
% 0.20/0.50               (k3_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ X16 @ 
% 0.20/0.50                X18))
% 0.20/0.50          | (r1_tmap_1 @ X15 @ X19 @ 
% 0.20/0.50             (k1_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.20/0.50              (u1_struct_0 @ X17) @ (u1_struct_0 @ X19) @ X16 @ X20) @ 
% 0.20/0.50             X18)
% 0.20/0.50          | ~ (r1_tmap_1 @ X15 @ X17 @ X16 @ X18)
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))))
% 0.20/0.50          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (v1_funct_1 @ X16)
% 0.20/0.50          | ~ (l1_pre_topc @ X15)
% 0.20/0.50          | ~ (v2_pre_topc @ X15)
% 0.20/0.50          | (v2_struct_0 @ X15))),
% 0.20/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 0.20/0.50             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ X1 @ sk_E) @ 
% 0.20/0.50             X2)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ 
% 0.20/0.50               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.50                X2))
% 0.20/0.50          | ~ (m1_subset_1 @ 
% 0.20/0.50               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.50                X2) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               (u1_struct_0 @ sk_B_2))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B_2)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B_2)
% 0.20/0.50          | (v2_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain, ((l1_pre_topc @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, ((v2_pre_topc @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_B_2 @ 
% 0.20/0.50             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ X1 @ sk_E) @ 
% 0.20/0.50             X2)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_A @ sk_B_2 @ sk_E @ 
% 0.20/0.50               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.50                X2))
% 0.20/0.50          | ~ (m1_subset_1 @ 
% 0.20/0.50               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.50                X2) @ 
% 0.20/0.50               (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['26', '27', '28', '29', '30', '31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (m1_subset_1 @ 
% 0.20/0.50             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              sk_D_1 @ sk_F) @ 
% 0.20/0.50             (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B_2 @ 
% 0.20/0.50           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_D_1 @ sk_E) @ 
% 0.20/0.50           sk_F)
% 0.20/0.50        | ~ (r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.20/0.50             (k1_zfmisc_1 @ 
% 0.20/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.20/0.50        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_C)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '33'])).
% 0.20/0.50  thf('35', plain, ((r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (m1_subset_1 @ 
% 0.20/0.50             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              sk_D_1 @ sk_F) @ 
% 0.20/0.50             (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B_2 @ 
% 0.20/0.50           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_D_1 @ sk_E) @ 
% 0.20/0.50           sk_F)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['34', '35', '36', '37', '38', '39', '40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C)
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B_2 @ 
% 0.20/0.50           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_D_1 @ sk_E) @ 
% 0.20/0.50           sk_F)
% 0.20/0.50        | ~ (m1_subset_1 @ 
% 0.20/0.50             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50              sk_D_1 @ sk_F) @ 
% 0.20/0.50             (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B_2 @ 
% 0.20/0.50           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_D_1 @ sk_E) @ 
% 0.20/0.50           sk_F)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C)
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B_2 @ 
% 0.20/0.50           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_D_1 @ sk_E) @ 
% 0.20/0.50           sk_F)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (~ (r1_tmap_1 @ sk_C @ sk_B_2 @ 
% 0.20/0.50          (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_D_1 @ sk_E) @ 
% 0.20/0.50          sk_F)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf(rc7_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ?[B:$i]:
% 0.20/0.50         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (sk_B_1 @ X10) @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.50          | ~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (v2_pre_topc @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.20/0.50  thf(t5_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.50          | ~ (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_C)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B_2)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_C))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.50          | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '50'])).
% 0.20/0.50  thf('52', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_C)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B_2)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_C))
% 0.20/0.50          | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_C))
% 0.20/0.50          | (v2_struct_0 @ sk_B_2)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((v1_xboole_0 @ (sk_B_1 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (sk_B_1 @ X10))
% 0.20/0.50          | ~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (v2_pre_topc @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_C)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B_2)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_2))),
% 0.20/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('64', plain, (((v2_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
