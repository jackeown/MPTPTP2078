%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0hYe2Yvc7y

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:09 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  214 (1141 expanded)
%              Number of leaves         :   33 ( 326 expanded)
%              Depth                    :   23
%              Number of atoms          : 2685 (65032 expanded)
%              Number of equality atoms :   54 ( 741 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t80_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ! [G: $i] :
                              ( ( ( v1_funct_1 @ G )
                                & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( D = A )
                                  & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                               => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( ( D = A )
                                    & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                                 => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                  <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_tmap_1])).

thf('0',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( X7 = X11 )
      | ~ ( r1_funct_2 @ X8 @ X9 @ X12 @ X10 @ X7 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( sk_E = sk_G ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('33',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( ( k3_tmap_1 @ X19 @ X17 @ X20 @ X18 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) @ X21 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('50',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d4_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( k2_tmap_1 @ X15 @ X13 @ X16 @ X14 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('72',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('75',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74','75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('84',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','38','83'])).

thf('85',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('87',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['36','37'])).

thf('88',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['87','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('94',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X23 @ X25 @ X24 @ X22 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('105',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('112',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ( X2 = X5 )
      | ~ ( r2_funct_2 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('115',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('116',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('117',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X23 @ X25 @ X24 @ X22 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['115','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('126',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('134',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('135',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('136',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X23 @ X25 @ X24 @ X22 @ X26 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('139',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['134','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55'])).

thf('145',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['133','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','132','151'])).

thf('153',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['92','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['86','157'])).

thf('159',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('160',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_F @ sk_F )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ( r2_funct_2 @ X3 @ X4 @ X2 @ X5 )
      | ( X2 != X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('165',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_funct_2 @ X3 @ X4 @ X5 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['163','165'])).

thf('167',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['162','169'])).

thf('171',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['85','170'])).

thf('172',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['84','171'])).

thf('173',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['88'])).

thf('174',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['88'])).

thf('177',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['85','170','176'])).

thf('178',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['175','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['172','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0hYe2Yvc7y
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 307 iterations in 0.163s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.36/0.62  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.62  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.36/0.62  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.62  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.62  thf(t80_tmap_1, conjecture,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.62             ( l1_pre_topc @ B ) ) =>
% 0.36/0.62           ( ![C:$i]:
% 0.36/0.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.62               ( ![D:$i]:
% 0.36/0.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.62                   ( ![E:$i]:
% 0.36/0.62                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.62                         ( v1_funct_2 @
% 0.36/0.62                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                         ( m1_subset_1 @
% 0.36/0.62                           E @ 
% 0.36/0.62                           ( k1_zfmisc_1 @
% 0.36/0.62                             ( k2_zfmisc_1 @
% 0.36/0.62                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                       ( ![F:$i]:
% 0.36/0.62                         ( ( ( v1_funct_1 @ F ) & 
% 0.36/0.62                             ( v1_funct_2 @
% 0.36/0.62                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                             ( m1_subset_1 @
% 0.36/0.62                               F @ 
% 0.36/0.62                               ( k1_zfmisc_1 @
% 0.36/0.62                                 ( k2_zfmisc_1 @
% 0.36/0.62                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                           ( ![G:$i]:
% 0.36/0.62                             ( ( ( v1_funct_1 @ G ) & 
% 0.36/0.62                                 ( v1_funct_2 @
% 0.36/0.62                                   G @ ( u1_struct_0 @ D ) @ 
% 0.36/0.62                                   ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                                 ( m1_subset_1 @
% 0.36/0.62                                   G @ 
% 0.36/0.62                                   ( k1_zfmisc_1 @
% 0.36/0.62                                     ( k2_zfmisc_1 @
% 0.36/0.62                                       ( u1_struct_0 @ D ) @ 
% 0.36/0.62                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                               ( ( ( ( D ) = ( A ) ) & 
% 0.36/0.62                                   ( r1_funct_2 @
% 0.36/0.62                                     ( u1_struct_0 @ A ) @ 
% 0.36/0.62                                     ( u1_struct_0 @ B ) @ 
% 0.36/0.62                                     ( u1_struct_0 @ D ) @ 
% 0.36/0.62                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.36/0.62                                 ( ( r2_funct_2 @
% 0.36/0.62                                     ( u1_struct_0 @ C ) @ 
% 0.36/0.62                                     ( u1_struct_0 @ B ) @ 
% 0.36/0.62                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.36/0.62                                   ( r2_funct_2 @
% 0.36/0.62                                     ( u1_struct_0 @ C ) @ 
% 0.36/0.62                                     ( u1_struct_0 @ B ) @ 
% 0.36/0.62                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i]:
% 0.36/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.62            ( l1_pre_topc @ A ) ) =>
% 0.36/0.62          ( ![B:$i]:
% 0.36/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.62                ( l1_pre_topc @ B ) ) =>
% 0.36/0.62              ( ![C:$i]:
% 0.36/0.62                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.62                  ( ![D:$i]:
% 0.36/0.62                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.62                      ( ![E:$i]:
% 0.36/0.62                        ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.62                            ( v1_funct_2 @
% 0.36/0.62                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                            ( m1_subset_1 @
% 0.36/0.62                              E @ 
% 0.36/0.62                              ( k1_zfmisc_1 @
% 0.36/0.62                                ( k2_zfmisc_1 @
% 0.36/0.62                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                          ( ![F:$i]:
% 0.36/0.62                            ( ( ( v1_funct_1 @ F ) & 
% 0.36/0.62                                ( v1_funct_2 @
% 0.36/0.62                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                                ( m1_subset_1 @
% 0.36/0.62                                  F @ 
% 0.36/0.62                                  ( k1_zfmisc_1 @
% 0.36/0.62                                    ( k2_zfmisc_1 @
% 0.36/0.62                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                              ( ![G:$i]:
% 0.36/0.62                                ( ( ( v1_funct_1 @ G ) & 
% 0.36/0.62                                    ( v1_funct_2 @
% 0.36/0.62                                      G @ ( u1_struct_0 @ D ) @ 
% 0.36/0.62                                      ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                                    ( m1_subset_1 @
% 0.36/0.62                                      G @ 
% 0.36/0.62                                      ( k1_zfmisc_1 @
% 0.36/0.62                                        ( k2_zfmisc_1 @
% 0.36/0.62                                          ( u1_struct_0 @ D ) @ 
% 0.36/0.62                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                                  ( ( ( ( D ) = ( A ) ) & 
% 0.36/0.62                                      ( r1_funct_2 @
% 0.36/0.62                                        ( u1_struct_0 @ A ) @ 
% 0.36/0.62                                        ( u1_struct_0 @ B ) @ 
% 0.36/0.62                                        ( u1_struct_0 @ D ) @ 
% 0.36/0.62                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.36/0.62                                    ( ( r2_funct_2 @
% 0.36/0.62                                        ( u1_struct_0 @ C ) @ 
% 0.36/0.62                                        ( u1_struct_0 @ B ) @ 
% 0.36/0.62                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.36/0.62                                      ( r2_funct_2 @
% 0.36/0.62                                        ( u1_struct_0 @ C ) @ 
% 0.36/0.62                                        ( u1_struct_0 @ B ) @ 
% 0.36/0.62                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)
% 0.36/0.62        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62             (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.36/0.62         <= (~
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('2', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.36/0.62         <= (~
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('5', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 0.36/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('8', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf(redefinition_r1_funct_2, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.62     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.36/0.62         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.62         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.36/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.36/0.62       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.36/0.62          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 0.36/0.62          | ~ (v1_funct_1 @ X7)
% 0.36/0.62          | (v1_xboole_0 @ X10)
% 0.36/0.62          | (v1_xboole_0 @ X9)
% 0.36/0.62          | ~ (v1_funct_1 @ X11)
% 0.36/0.62          | ~ (v1_funct_2 @ X11 @ X12 @ X10)
% 0.36/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.36/0.62          | ((X7) = (X11))
% 0.36/0.62          | ~ (r1_funct_2 @ X8 @ X9 @ X12 @ X10 @ X7 @ X11))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 0.36/0.62             X1 @ sk_E @ X0)
% 0.36/0.62          | ((sk_E) = (X0))
% 0.36/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | (v1_xboole_0 @ X1)
% 0.36/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.62               (u1_struct_0 @ sk_B_1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf('12', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('14', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 0.36/0.62             X1 @ sk_E @ X0)
% 0.36/0.62          | ((sk_E) = (X0))
% 0.36/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | (v1_xboole_0 @ X1))),
% 0.36/0.62      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | ~ (v1_funct_1 @ sk_G)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | ~ (m1_subset_1 @ sk_G @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62        | ((sk_E) = (sk_G)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['6', '16'])).
% 0.36/0.62  thf('18', plain, ((v1_funct_1 @ sk_G)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_G @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | ((sk_E) = (sk_G)))),
% 0.36/0.62      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.36/0.62  thf(rc7_pre_topc, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.62       ( ?[B:$i]:
% 0.36/0.62         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.62           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X6 : $i]:
% 0.36/0.62         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.36/0.62          | ~ (l1_pre_topc @ X6)
% 0.36/0.62          | ~ (v2_pre_topc @ X6)
% 0.36/0.62          | (v2_struct_0 @ X6))),
% 0.36/0.62      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.36/0.62  thf(cc1_subset_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.62          | (v1_xboole_0 @ X0)
% 0.36/0.62          | ~ (v1_xboole_0 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ X0)
% 0.36/0.62          | ~ (v2_pre_topc @ X0)
% 0.36/0.62          | ~ (l1_pre_topc @ X0)
% 0.36/0.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.36/0.62          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      ((((sk_E) = (sk_G))
% 0.36/0.62        | (v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.36/0.62        | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.62        | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.62  thf('27', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('28', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      ((((sk_E) = (sk_G))
% 0.36/0.62        | (v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.36/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.36/0.62  thf('30', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('31', plain, (((v1_xboole_0 @ (sk_B @ sk_B_1)) | ((sk_E) = (sk_G)))),
% 0.36/0.62      inference('clc', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('32', plain,
% 0.36/0.62      (![X6 : $i]:
% 0.36/0.62         (~ (v1_xboole_0 @ (sk_B @ X6))
% 0.36/0.62          | ~ (l1_pre_topc @ X6)
% 0.36/0.62          | ~ (v2_pre_topc @ X6)
% 0.36/0.62          | (v2_struct_0 @ X6))),
% 0.36/0.62      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.36/0.62  thf('33', plain,
% 0.36/0.62      ((((sk_E) = (sk_G))
% 0.36/0.62        | (v2_struct_0 @ sk_B_1)
% 0.36/0.62        | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62        | ~ (l1_pre_topc @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf('34', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('35', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('36', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.36/0.62  thf('37', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('38', plain, (((sk_E) = (sk_G))),
% 0.36/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.36/0.62  thf('39', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('40', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.62  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('43', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf(d5_tmap_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.62             ( l1_pre_topc @ B ) ) =>
% 0.36/0.62           ( ![C:$i]:
% 0.36/0.62             ( ( m1_pre_topc @ C @ A ) =>
% 0.36/0.62               ( ![D:$i]:
% 0.36/0.62                 ( ( m1_pre_topc @ D @ A ) =>
% 0.36/0.62                   ( ![E:$i]:
% 0.36/0.62                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.62                         ( v1_funct_2 @
% 0.36/0.62                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                         ( m1_subset_1 @
% 0.36/0.62                           E @ 
% 0.36/0.62                           ( k1_zfmisc_1 @
% 0.36/0.62                             ( k2_zfmisc_1 @
% 0.36/0.62                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                       ( ( m1_pre_topc @ D @ C ) =>
% 0.36/0.62                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.36/0.62                           ( k2_partfun1 @
% 0.36/0.62                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.36/0.62                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.62  thf('46', plain,
% 0.36/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.62         ((v2_struct_0 @ X17)
% 0.36/0.62          | ~ (v2_pre_topc @ X17)
% 0.36/0.62          | ~ (l1_pre_topc @ X17)
% 0.36/0.62          | ~ (m1_pre_topc @ X18 @ X19)
% 0.36/0.62          | ~ (m1_pre_topc @ X18 @ X20)
% 0.36/0.62          | ((k3_tmap_1 @ X19 @ X17 @ X20 @ X18 @ X21)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17) @ 
% 0.36/0.62                 X21 @ (u1_struct_0 @ X18)))
% 0.36/0.62          | ~ (m1_subset_1 @ X21 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17))))
% 0.36/0.62          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17))
% 0.36/0.62          | ~ (v1_funct_1 @ X21)
% 0.36/0.62          | ~ (m1_pre_topc @ X20 @ X19)
% 0.36/0.62          | ~ (l1_pre_topc @ X19)
% 0.36/0.62          | ~ (v2_pre_topc @ X19)
% 0.36/0.62          | (v2_struct_0 @ X19))),
% 0.36/0.62      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.36/0.62  thf('47', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((v2_struct_0 @ X0)
% 0.36/0.62          | ~ (v2_pre_topc @ X0)
% 0.36/0.62          | ~ (l1_pre_topc @ X0)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.62               (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X1)))
% 0.36/0.62          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.62          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.62  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('49', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('50', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('51', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('52', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((v2_struct_0 @ X0)
% 0.36/0.62          | ~ (v2_pre_topc @ X0)
% 0.36/0.62          | ~ (l1_pre_topc @ X0)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.36/0.62          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X1)))
% 0.36/0.62          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.36/0.62          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.36/0.62  thf('53', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.62          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_D))),
% 0.36/0.62      inference('sup-', [status(thm)], ['44', '52'])).
% 0.36/0.62  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('55', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('56', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('58', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('59', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.62  thf('60', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.62          | (v2_struct_0 @ sk_D))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '59'])).
% 0.36/0.62  thf('61', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ sk_D)
% 0.36/0.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.36/0.62  thf('62', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_B_1)
% 0.36/0.62        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.36/0.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               sk_E @ (u1_struct_0 @ sk_C)))
% 0.36/0.62        | (v2_struct_0 @ sk_D))),
% 0.36/0.62      inference('sup-', [status(thm)], ['41', '61'])).
% 0.36/0.62  thf('63', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('64', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_D)
% 0.36/0.62        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.36/0.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.36/0.62      inference('clc', [status(thm)], ['62', '63'])).
% 0.36/0.62  thf('65', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('66', plain,
% 0.36/0.62      (((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.36/0.62         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62            sk_E @ (u1_struct_0 @ sk_C)))),
% 0.36/0.62      inference('clc', [status(thm)], ['64', '65'])).
% 0.36/0.62  thf('67', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.62  thf('68', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf(d4_tmap_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.62             ( l1_pre_topc @ B ) ) =>
% 0.36/0.62           ( ![C:$i]:
% 0.36/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                 ( m1_subset_1 @
% 0.36/0.62                   C @ 
% 0.36/0.62                   ( k1_zfmisc_1 @
% 0.36/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62               ( ![D:$i]:
% 0.36/0.62                 ( ( m1_pre_topc @ D @ A ) =>
% 0.36/0.62                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.36/0.62                     ( k2_partfun1 @
% 0.36/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.62                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.62  thf('69', plain,
% 0.36/0.62      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.62         ((v2_struct_0 @ X13)
% 0.36/0.62          | ~ (v2_pre_topc @ X13)
% 0.36/0.62          | ~ (l1_pre_topc @ X13)
% 0.36/0.62          | ~ (m1_pre_topc @ X14 @ X15)
% 0.36/0.62          | ((k2_tmap_1 @ X15 @ X13 @ X16 @ X14)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ 
% 0.36/0.62                 X16 @ (u1_struct_0 @ X14)))
% 0.36/0.62          | ~ (m1_subset_1 @ X16 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.36/0.62          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.36/0.62          | ~ (v1_funct_1 @ X16)
% 0.36/0.62          | ~ (l1_pre_topc @ X15)
% 0.36/0.62          | ~ (v2_pre_topc @ X15)
% 0.36/0.62          | (v2_struct_0 @ X15))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.36/0.62  thf('70', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ sk_D)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.62               (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.36/0.62  thf('71', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.62  thf('72', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('74', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('75', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('76', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('77', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ sk_D)
% 0.36/0.62          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 0.36/0.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62                 sk_E @ (u1_struct_0 @ X0)))
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)],
% 0.36/0.62                ['70', '71', '72', '73', '74', '75', '76'])).
% 0.36/0.62  thf('78', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_B_1)
% 0.36/0.62        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C)
% 0.36/0.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               sk_E @ (u1_struct_0 @ sk_C)))
% 0.36/0.62        | (v2_struct_0 @ sk_D))),
% 0.36/0.62      inference('sup-', [status(thm)], ['67', '77'])).
% 0.36/0.62  thf('79', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('80', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_D)
% 0.36/0.62        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C)
% 0.36/0.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.36/0.62      inference('clc', [status(thm)], ['78', '79'])).
% 0.36/0.62  thf('81', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('82', plain,
% 0.36/0.62      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C)
% 0.36/0.62         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62            sk_E @ (u1_struct_0 @ sk_C)))),
% 0.36/0.62      inference('clc', [status(thm)], ['80', '81'])).
% 0.36/0.62  thf('83', plain,
% 0.36/0.62      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C)
% 0.36/0.62         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E))),
% 0.36/0.62      inference('sup+', [status(thm)], ['66', '82'])).
% 0.36/0.62  thf('84', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C) @ sk_F))
% 0.36/0.62         <= (~
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('demod', [status(thm)], ['3', '38', '83'])).
% 0.36/0.62  thf('85', plain,
% 0.36/0.62      (~
% 0.36/0.62       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 0.36/0.62       ~
% 0.36/0.62       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('86', plain,
% 0.36/0.62      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C)
% 0.36/0.62         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E))),
% 0.36/0.62      inference('sup+', [status(thm)], ['66', '82'])).
% 0.36/0.62  thf('87', plain, (((sk_E) = (sk_G))),
% 0.36/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.36/0.62  thf('88', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)
% 0.36/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('89', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('split', [status(esa)], ['88'])).
% 0.36/0.62  thf('90', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('91', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('demod', [status(thm)], ['89', '90'])).
% 0.36/0.62  thf('92', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['87', '91'])).
% 0.36/0.62  thf('93', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.62  thf('94', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.62  thf('95', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf(dt_k3_tmap_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.62         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.36/0.62         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.36/0.62         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.36/0.62         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62         ( m1_subset_1 @
% 0.36/0.62           E @ 
% 0.36/0.62           ( k1_zfmisc_1 @
% 0.36/0.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.36/0.62         ( v1_funct_2 @
% 0.36/0.62           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.36/0.62           ( u1_struct_0 @ B ) ) & 
% 0.36/0.62         ( m1_subset_1 @
% 0.36/0.62           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.36/0.62           ( k1_zfmisc_1 @
% 0.36/0.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.36/0.62  thf('96', plain,
% 0.36/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.36/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.36/0.62          | ~ (l1_pre_topc @ X25)
% 0.36/0.62          | ~ (v2_pre_topc @ X25)
% 0.36/0.62          | (v2_struct_0 @ X25)
% 0.36/0.62          | ~ (l1_pre_topc @ X23)
% 0.36/0.62          | ~ (v2_pre_topc @ X23)
% 0.36/0.62          | (v2_struct_0 @ X23)
% 0.36/0.62          | ~ (v1_funct_1 @ X26)
% 0.36/0.62          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 0.36/0.62          | ~ (m1_subset_1 @ X26 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 0.36/0.62          | (m1_subset_1 @ (k3_tmap_1 @ X23 @ X25 @ X24 @ X22 @ X26) @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25)))))),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.36/0.62  thf('97', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.62               (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.62          | (v2_struct_0 @ X1)
% 0.36/0.62          | ~ (v2_pre_topc @ X1)
% 0.36/0.62          | ~ (l1_pre_topc @ X1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.62  thf('98', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('100', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('101', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('102', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62          | (v2_struct_0 @ X1)
% 0.36/0.62          | ~ (v2_pre_topc @ X1)
% 0.36/0.62          | ~ (l1_pre_topc @ X1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.36/0.62      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.36/0.62  thf('103', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_D)
% 0.36/0.62          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['94', '102'])).
% 0.36/0.62  thf('104', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('105', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.62  thf('106', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | (v2_struct_0 @ sk_D)
% 0.36/0.62          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))))),
% 0.36/0.62      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.36/0.62  thf('107', plain,
% 0.36/0.62      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62        | (v2_struct_0 @ sk_D)
% 0.36/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['93', '106'])).
% 0.36/0.62  thf('108', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('109', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_B_1)
% 0.36/0.62        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1)))))),
% 0.36/0.62      inference('clc', [status(thm)], ['107', '108'])).
% 0.36/0.62  thf('110', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('111', plain,
% 0.36/0.62      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('clc', [status(thm)], ['109', '110'])).
% 0.36/0.62  thf(redefinition_r2_funct_2, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.62         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.62       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.62  thf('112', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.36/0.62          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.36/0.62          | ~ (v1_funct_1 @ X2)
% 0.36/0.62          | ~ (v1_funct_1 @ X5)
% 0.36/0.62          | ~ (v1_funct_2 @ X5 @ X3 @ X4)
% 0.36/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.36/0.62          | ((X2) = (X5))
% 0.36/0.62          | ~ (r2_funct_2 @ X3 @ X4 @ X2 @ X5))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.36/0.62  thf('113', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62             (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ X0)
% 0.36/0.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) = (X0))
% 0.36/0.62          | ~ (m1_subset_1 @ X0 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E))
% 0.36/0.62          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['111', '112'])).
% 0.36/0.62  thf('114', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.62  thf('115', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.62  thf('116', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf('117', plain,
% 0.36/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.36/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.36/0.62          | ~ (l1_pre_topc @ X25)
% 0.36/0.62          | ~ (v2_pre_topc @ X25)
% 0.36/0.62          | (v2_struct_0 @ X25)
% 0.36/0.62          | ~ (l1_pre_topc @ X23)
% 0.36/0.62          | ~ (v2_pre_topc @ X23)
% 0.36/0.62          | (v2_struct_0 @ X23)
% 0.36/0.62          | ~ (v1_funct_1 @ X26)
% 0.36/0.62          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 0.36/0.62          | ~ (m1_subset_1 @ X26 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 0.36/0.62          | (v1_funct_1 @ (k3_tmap_1 @ X23 @ X25 @ X24 @ X22 @ X26)))),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.36/0.62  thf('118', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E))
% 0.36/0.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.62               (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.62          | (v2_struct_0 @ X1)
% 0.36/0.62          | ~ (v2_pre_topc @ X1)
% 0.36/0.62          | ~ (l1_pre_topc @ X1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['116', '117'])).
% 0.36/0.62  thf('119', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('121', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('122', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('123', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E))
% 0.36/0.62          | (v2_struct_0 @ X1)
% 0.36/0.62          | ~ (v2_pre_topc @ X1)
% 0.36/0.62          | ~ (l1_pre_topc @ X1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.36/0.62      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 0.36/0.62  thf('124', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_D)
% 0.36/0.62          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['115', '123'])).
% 0.36/0.62  thf('125', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('126', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.62  thf('127', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | (v2_struct_0 @ sk_D)
% 0.36/0.62          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)))),
% 0.36/0.62      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.36/0.62  thf('128', plain,
% 0.36/0.62      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E))
% 0.36/0.62        | (v2_struct_0 @ sk_D)
% 0.36/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['114', '127'])).
% 0.36/0.62  thf('129', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('130', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_B_1)
% 0.36/0.62        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E)))),
% 0.36/0.62      inference('clc', [status(thm)], ['128', '129'])).
% 0.36/0.62  thf('131', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('132', plain,
% 0.36/0.62      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E))),
% 0.36/0.62      inference('clc', [status(thm)], ['130', '131'])).
% 0.36/0.62  thf('133', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.62  thf('134', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.62  thf('135', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_E @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.62  thf('136', plain,
% 0.36/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.36/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.36/0.62          | ~ (l1_pre_topc @ X25)
% 0.36/0.62          | ~ (v2_pre_topc @ X25)
% 0.36/0.62          | (v2_struct_0 @ X25)
% 0.36/0.62          | ~ (l1_pre_topc @ X23)
% 0.36/0.62          | ~ (v2_pre_topc @ X23)
% 0.36/0.62          | (v2_struct_0 @ X23)
% 0.36/0.62          | ~ (v1_funct_1 @ X26)
% 0.36/0.62          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 0.36/0.62          | ~ (m1_subset_1 @ X26 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 0.36/0.62          | (v1_funct_2 @ (k3_tmap_1 @ X23 @ X25 @ X24 @ X22 @ X26) @ 
% 0.36/0.62             (u1_struct_0 @ X22) @ (u1_struct_0 @ X25)))),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.36/0.62  thf('137', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.62               (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.62          | (v2_struct_0 @ X1)
% 0.36/0.62          | ~ (v2_pre_topc @ X1)
% 0.36/0.62          | ~ (l1_pre_topc @ X1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['135', '136'])).
% 0.36/0.62  thf('138', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('139', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('140', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('141', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('142', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | (v2_struct_0 @ X1)
% 0.36/0.62          | ~ (v2_pre_topc @ X1)
% 0.36/0.62          | ~ (l1_pre_topc @ X1)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.36/0.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.36/0.62      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.36/0.62  thf('143', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | ~ (l1_pre_topc @ sk_D)
% 0.36/0.62          | ~ (v2_pre_topc @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_D)
% 0.36/0.62          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['134', '142'])).
% 0.36/0.62  thf('144', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('145', plain, ((v2_pre_topc @ sk_D)),
% 0.36/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.62  thf('146', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.36/0.62          | (v2_struct_0 @ sk_B_1)
% 0.36/0.62          | (v2_struct_0 @ sk_D)
% 0.36/0.62          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E) @ 
% 0.36/0.62             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.62      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.36/0.62  thf('147', plain,
% 0.36/0.62      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | (v2_struct_0 @ sk_D)
% 0.36/0.62        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['133', '146'])).
% 0.36/0.62  thf('148', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('149', plain,
% 0.36/0.62      (((v2_struct_0 @ sk_B_1)
% 0.36/0.62        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.62      inference('clc', [status(thm)], ['147', '148'])).
% 0.36/0.62  thf('150', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('151', plain,
% 0.36/0.62      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.36/0.62        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('clc', [status(thm)], ['149', '150'])).
% 0.36/0.62  thf('152', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62             (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ X0)
% 0.36/0.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) = (X0))
% 0.36/0.62          | ~ (m1_subset_1 @ X0 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62          | ~ (v1_funct_1 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['113', '132', '151'])).
% 0.36/0.62  thf('153', plain,
% 0.36/0.62      (((~ (v1_funct_1 @ sk_F)
% 0.36/0.62         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62         | ~ (m1_subset_1 @ sk_F @ 
% 0.36/0.62              (k1_zfmisc_1 @ 
% 0.36/0.62               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.62         | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) = (sk_F))))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['92', '152'])).
% 0.36/0.62  thf('154', plain, ((v1_funct_1 @ sk_F)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('155', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('156', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_F @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('157', plain,
% 0.36/0.62      ((((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C @ sk_E) = (sk_F)))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 0.36/0.62  thf('158', plain,
% 0.36/0.62      ((((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C) = (sk_F)))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['86', '157'])).
% 0.36/0.62  thf('159', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F))
% 0.36/0.62         <= (~
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('160', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('161', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C) @ sk_F))
% 0.36/0.62         <= (~
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)))),
% 0.36/0.62      inference('demod', [status(thm)], ['159', '160'])).
% 0.36/0.62  thf('162', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_F @ 
% 0.36/0.62           sk_F))
% 0.36/0.62         <= (~
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)) & 
% 0.36/0.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['158', '161'])).
% 0.36/0.62  thf('163', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_F @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('164', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.36/0.62          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.36/0.62          | ~ (v1_funct_1 @ X2)
% 0.36/0.62          | ~ (v1_funct_1 @ X5)
% 0.36/0.62          | ~ (v1_funct_2 @ X5 @ X3 @ X4)
% 0.36/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.36/0.62          | (r2_funct_2 @ X3 @ X4 @ X2 @ X5)
% 0.36/0.62          | ((X2) != (X5)))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.36/0.62  thf('165', plain,
% 0.36/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.62         ((r2_funct_2 @ X3 @ X4 @ X5 @ X5)
% 0.36/0.62          | ~ (v1_funct_1 @ X5)
% 0.36/0.62          | ~ (v1_funct_2 @ X5 @ X3 @ X4)
% 0.36/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['164'])).
% 0.36/0.62  thf('166', plain,
% 0.36/0.62      ((~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.36/0.62        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_F @ 
% 0.36/0.62           sk_F))),
% 0.36/0.62      inference('sup-', [status(thm)], ['163', '165'])).
% 0.36/0.62  thf('167', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('168', plain, ((v1_funct_1 @ sk_F)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('169', plain,
% 0.36/0.62      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ sk_F @ 
% 0.36/0.62        sk_F)),
% 0.36/0.62      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.36/0.62  thf('170', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)) | 
% 0.36/0.62       ~
% 0.36/0.62       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.62      inference('demod', [status(thm)], ['162', '169'])).
% 0.36/0.62  thf('171', plain,
% 0.36/0.62      (~
% 0.36/0.62       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['85', '170'])).
% 0.36/0.62  thf('172', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62          (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C) @ sk_F)),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['84', '171'])).
% 0.36/0.62  thf('173', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)))),
% 0.36/0.62      inference('split', [status(esa)], ['88'])).
% 0.36/0.62  thf('174', plain, (((sk_D) = (sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('175', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C) @ sk_F))
% 0.36/0.62         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)))),
% 0.36/0.62      inference('demod', [status(thm)], ['173', '174'])).
% 0.36/0.62  thf('176', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F)) | 
% 0.36/0.62       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.62      inference('split', [status(esa)], ['88'])).
% 0.36/0.62  thf('177', plain,
% 0.36/0.62      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C) @ sk_F))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['85', '170', '176'])).
% 0.36/0.62  thf('178', plain,
% 0.36/0.62      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.62        (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C) @ sk_F)),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['175', '177'])).
% 0.36/0.62  thf('179', plain, ($false), inference('demod', [status(thm)], ['172', '178'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
