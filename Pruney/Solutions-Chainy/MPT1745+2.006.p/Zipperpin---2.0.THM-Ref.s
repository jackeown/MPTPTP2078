%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kDGJgIipTP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 163 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          : 1233 (6647 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ X1 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X1 @ X2 @ X0 @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X6 @ X8 )
      | ( r1_tmap_1 @ X6 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ sk_E @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_pre_topc @ sk_E @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','17','18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_tmap_1 @ X10 @ X12 @ X11 @ X13 )
      | ( r1_tmap_1 @ X10 @ X14 @ ( k1_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) @ X11 @ X15 ) @ X13 )
      | ( X16
       != ( k3_funct_2 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) @ X11 @ X13 ) )
      | ~ ( r1_tmap_1 @ X12 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) @ X11 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_tmap_1 @ X12 @ X14 @ X15 @ ( k3_funct_2 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) @ X11 @ X13 ) )
      | ( r1_tmap_1 @ X10 @ X14 @ ( k1_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) @ X11 @ X15 ) @ X13 )
      | ~ ( r1_tmap_1 @ X10 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kDGJgIipTP
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 46 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(t54_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.49                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.49                     ( v1_funct_2 @
% 0.20/0.49                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49                     ( m1_subset_1 @
% 0.20/0.49                       D @ 
% 0.20/0.49                       ( k1_zfmisc_1 @
% 0.20/0.49                         ( k2_zfmisc_1 @
% 0.20/0.49                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                         ( v1_funct_2 @
% 0.20/0.49                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                         ( m1_subset_1 @
% 0.20/0.49                           E @ 
% 0.20/0.49                           ( k1_zfmisc_1 @
% 0.20/0.49                             ( k2_zfmisc_1 @
% 0.20/0.49                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                       ( ![F:$i]:
% 0.20/0.49                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.49                           ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.20/0.49                               ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.20/0.49                             ( r1_tmap_1 @
% 0.20/0.49                               C @ B @ 
% 0.20/0.49                               ( k1_partfun1 @
% 0.20/0.49                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.49                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.49                                 D @ E ) @ 
% 0.20/0.49                               F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49                ( l1_pre_topc @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.49                    ( l1_pre_topc @ C ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.49                        ( v1_funct_2 @
% 0.20/0.49                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49                        ( m1_subset_1 @
% 0.20/0.49                          D @ 
% 0.20/0.49                          ( k1_zfmisc_1 @
% 0.20/0.49                            ( k2_zfmisc_1 @
% 0.20/0.49                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.49                      ( ![E:$i]:
% 0.20/0.49                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                            ( v1_funct_2 @
% 0.20/0.49                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                            ( m1_subset_1 @
% 0.20/0.49                              E @ 
% 0.20/0.49                              ( k1_zfmisc_1 @
% 0.20/0.49                                ( k2_zfmisc_1 @
% 0.20/0.49                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                          ( ![F:$i]:
% 0.20/0.49                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.49                              ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.20/0.49                                  ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.20/0.49                                ( r1_tmap_1 @
% 0.20/0.49                                  C @ B @ 
% 0.20/0.49                                  ( k1_partfun1 @
% 0.20/0.49                                    ( u1_struct_0 @ C ) @ 
% 0.20/0.49                                    ( u1_struct_0 @ A ) @ 
% 0.20/0.49                                    ( u1_struct_0 @ A ) @ 
% 0.20/0.49                                    ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.20/0.49                                  F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t54_tmap_1])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k3_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.20/0.49          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | (v1_xboole_0 @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ X1)
% 0.20/0.49          | (m1_subset_1 @ (k3_funct_2 @ X1 @ X2 @ X0 @ X3) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ 
% 0.20/0.49           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            sk_D_1 @ X0) @ 
% 0.20/0.49           (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.49               (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ 
% 0.20/0.49           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            sk_D_1 @ X0) @ 
% 0.20/0.49           (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (m1_subset_1 @ 
% 0.20/0.49           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            sk_D_1 @ sk_F) @ 
% 0.20/0.49           (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (m1_subset_1 @ 
% 0.20/0.49           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            sk_D_1 @ sk_F) @ 
% 0.20/0.49           (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t49_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49                 ( m1_subset_1 @
% 0.20/0.49                   C @ 
% 0.20/0.49                   ( k1_zfmisc_1 @
% 0.20/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.49               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X6)
% 0.20/0.49          | ~ (v2_pre_topc @ X6)
% 0.20/0.49          | ~ (l1_pre_topc @ X6)
% 0.20/0.49          | ~ (v5_pre_topc @ X7 @ X6 @ X8)
% 0.20/0.49          | (r1_tmap_1 @ X6 @ X8 @ X7 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X8))))
% 0.20/0.49          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (v1_funct_1 @ X7)
% 0.20/0.49          | ~ (l1_pre_topc @ X8)
% 0.20/0.49          | ~ (v2_pre_topc @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.20/0.49          | ~ (v5_pre_topc @ sk_E @ sk_A @ sk_B)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v5_pre_topc @ sk_E @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['12', '13', '14', '15', '16', '17', '18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ 
% 0.20/0.49           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            sk_D_1 @ sk_F))
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t52_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.49                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.49                     ( v1_funct_2 @
% 0.20/0.49                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.49                     ( m1_subset_1 @
% 0.20/0.49                       D @ 
% 0.20/0.49                       ( k1_zfmisc_1 @
% 0.20/0.49                         ( k2_zfmisc_1 @
% 0.20/0.49                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                         ( v1_funct_2 @
% 0.20/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49                         ( m1_subset_1 @
% 0.20/0.49                           E @ 
% 0.20/0.49                           ( k1_zfmisc_1 @
% 0.20/0.49                             ( k2_zfmisc_1 @
% 0.20/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.49                       ( ![F:$i]:
% 0.20/0.49                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                           ( ![G:$i]:
% 0.20/0.49                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.49                               ( ( ( ( G ) =
% 0.20/0.49                                     ( k3_funct_2 @
% 0.20/0.49                                       ( u1_struct_0 @ B ) @ 
% 0.20/0.49                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.20/0.49                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.20/0.49                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.20/0.49                                 ( r1_tmap_1 @
% 0.20/0.49                                   B @ A @ 
% 0.20/0.49                                   ( k1_partfun1 @
% 0.20/0.49                                     ( u1_struct_0 @ B ) @ 
% 0.20/0.49                                     ( u1_struct_0 @ C ) @ 
% 0.20/0.49                                     ( u1_struct_0 @ C ) @ 
% 0.20/0.49                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.20/0.49                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X10)
% 0.20/0.49          | ~ (v2_pre_topc @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (m1_subset_1 @ X11 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))))
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.20/0.49          | ~ (r1_tmap_1 @ X10 @ X12 @ X11 @ X13)
% 0.20/0.49          | (r1_tmap_1 @ X10 @ X14 @ 
% 0.20/0.49             (k1_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12) @ 
% 0.20/0.49              (u1_struct_0 @ X12) @ (u1_struct_0 @ X14) @ X11 @ X15) @ 
% 0.20/0.49             X13)
% 0.20/0.49          | ((X16)
% 0.20/0.49              != (k3_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12) @ 
% 0.20/0.49                  X11 @ X13))
% 0.20/0.49          | ~ (r1_tmap_1 @ X12 @ X14 @ X15 @ X16)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))))
% 0.20/0.49          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))
% 0.20/0.49          | ~ (v1_funct_1 @ X15)
% 0.20/0.49          | ~ (l1_pre_topc @ X12)
% 0.20/0.49          | ~ (v2_pre_topc @ X12)
% 0.20/0.49          | (v2_struct_0 @ X12)
% 0.20/0.49          | ~ (l1_pre_topc @ X14)
% 0.20/0.49          | ~ (v2_pre_topc @ X14)
% 0.20/0.49          | (v2_struct_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X14)
% 0.20/0.49          | ~ (v2_pre_topc @ X14)
% 0.20/0.49          | ~ (l1_pre_topc @ X14)
% 0.20/0.49          | (v2_struct_0 @ X12)
% 0.20/0.49          | ~ (v2_pre_topc @ X12)
% 0.20/0.49          | ~ (l1_pre_topc @ X12)
% 0.20/0.49          | ~ (v1_funct_1 @ X15)
% 0.20/0.49          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))))
% 0.20/0.49          | ~ (m1_subset_1 @ 
% 0.20/0.49               (k3_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12) @ X11 @ 
% 0.20/0.49                X13) @ 
% 0.20/0.49               (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (r1_tmap_1 @ X12 @ X14 @ X15 @ 
% 0.20/0.49               (k3_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12) @ X11 @ 
% 0.20/0.49                X13))
% 0.20/0.49          | (r1_tmap_1 @ X10 @ X14 @ 
% 0.20/0.49             (k1_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12) @ 
% 0.20/0.49              (u1_struct_0 @ X12) @ (u1_struct_0 @ X14) @ X11 @ X15) @ 
% 0.20/0.49             X13)
% 0.20/0.49          | ~ (r1_tmap_1 @ X10 @ X12 @ X11 @ X13)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.20/0.49          | ~ (m1_subset_1 @ X11 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))))
% 0.20/0.49          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ~ (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (v2_pre_topc @ X10)
% 0.20/0.49          | (v2_struct_0 @ X10))),
% 0.20/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.20/0.49          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.49             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X1 @ sk_E) @ 
% 0.20/0.49             X2)
% 0.20/0.49          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ 
% 0.20/0.49               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.49                X2))
% 0.20/0.49          | ~ (m1_subset_1 @ 
% 0.20/0.49               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.49                X2) @ 
% 0.20/0.49               (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.20/0.49          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.49             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X1 @ sk_E) @ 
% 0.20/0.49             X2)
% 0.20/0.49          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ 
% 0.20/0.49               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.49                X2))
% 0.20/0.49          | ~ (m1_subset_1 @ 
% 0.20/0.49               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.20/0.49                X2) @ 
% 0.20/0.49               (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['25', '26', '27', '28', '29', '30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (m1_subset_1 @ 
% 0.20/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              sk_D_1 @ sk_F) @ 
% 0.20/0.49             (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.49           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.20/0.49           sk_F)
% 0.20/0.49        | ~ (r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)
% 0.20/0.49        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.20/0.49        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_C)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '32'])).
% 0.20/0.49  thf('34', plain, ((r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (m1_subset_1 @ 
% 0.20/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              sk_D_1 @ sk_F) @ 
% 0.20/0.49             (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.49           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.20/0.49           sk_F)
% 0.20/0.49        | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['33', '34', '35', '36', '37', '38', '39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_C)
% 0.20/0.49        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.49           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.20/0.49           sk_F)
% 0.20/0.49        | ~ (m1_subset_1 @ 
% 0.20/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              sk_D_1 @ sk_F) @ 
% 0.20/0.49             (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.49           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.20/0.49           sk_F)
% 0.20/0.49        | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_C)
% 0.20/0.49        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.49           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.20/0.49           sk_F)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.49          (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.20/0.49          sk_F)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X5 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (l1_struct_0 @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_C)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('50', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('51', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['48', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
