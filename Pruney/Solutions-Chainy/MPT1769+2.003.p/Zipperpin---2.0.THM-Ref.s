%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Phc7KAb0zK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:09 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  357 (5474 expanded)
%              Number of leaves         :   42 (1544 expanded)
%              Depth                    :   30
%              Number of atoms          : 4650 (303337 expanded)
%              Number of equality atoms :   87 (3630 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) @ X29 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14','17','18','21','26','27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v4_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X31 @ X32 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','53','54','55'])).

thf(t77_tmap_1,axiom,(
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
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ ( k3_tmap_1 @ X41 @ X39 @ X43 @ X40 @ X42 ) @ ( k2_tmap_1 @ X41 @ X39 @ X44 @ X40 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X39 ) @ X42 @ ( k2_tmap_1 @ X41 @ X39 @ X44 @ X43 ) )
      | ~ ( m1_pre_topc @ X40 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_pre_topc @ X43 @ X41 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['42','43'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_funct_2 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_funct_2 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['42','43'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['42','43'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('75',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['42','43'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('77',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('78',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('80',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('82',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','63','70','71','72','73','74','75','76','77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14','17','18','21','26','27','28'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('97',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('100',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('106',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_funct_2 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('116',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('117',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('118',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('121',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['116','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('127',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('135',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('136',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('137',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38 ) @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('140',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('146',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','133','152'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['93','153'])).

thf('155',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('156',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('157',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X31 @ X32 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('160',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('161',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162'])).

thf('164',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['155','163'])).

thf('165',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('166',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('167',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('169',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('171',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','171'])).

thf('173',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('174',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('175',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X31 @ X32 @ X30 @ X33 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('178',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('179',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['173','181'])).

thf('183',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['169','170'])).

thf('184',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','53','54','55'])).

thf('187',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['169','170'])).

thf('189',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['154','172','184','189'])).

thf('191',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['191'])).

thf('193',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','53','54','55'])).

thf('196',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_funct_2 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
        = sk_F )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['194','197'])).

thf('199',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('200',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('201',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('202',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','171'])).

thf('203',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('207',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['169','170'])).

thf('208',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203','204','205','206','207'])).

thf('209',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['212'])).

thf('214',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['214'])).

thf('216',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['213','217'])).

thf('219',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['222'])).

thf('224',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('228',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( X20 = X24 )
      | ~ ( r1_funct_2 @ X21 @ X22 @ X25 @ X23 @ X20 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['226','232'])).

thf('234',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('238',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('239',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('240',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('242',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['191'])).

thf('246',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['244','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','133','152'])).

thf('250',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['250','251','252','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('256',plain,
    ( ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','53','54','55'])).

thf('258',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_funct_2 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 )
      | ( sk_F = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 )
      | ( sk_F = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['257','263'])).

thf('265',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['169','170'])).

thf('266',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('268',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('269',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('270',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('271',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['266','267','268','269','270'])).

thf('272',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('273',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','171'])).

thf('275',plain,
    ( ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( sk_F
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['256','275'])).

thf('277',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('278',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['222'])).

thf('279',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,
    ( ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['276','279'])).

thf('281',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_funct_2 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('283',plain,
    ( ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('287',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['280','286'])).

thf('288',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['287','288'])).

thf('290',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['289','290'])).

thf('292',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('295',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['222'])).

thf('296',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['294','295'])).

thf('297',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['191'])).

thf('298',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['218','223','293','296','297'])).

thf('299',plain,
    ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    = sk_F ),
    inference(simpl_trail,[status(thm)],['208','298'])).

thf('300',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F ) ),
    inference(demod,[status(thm)],['190','299'])).

thf('301',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('302',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['242','243'])).

thf('303',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['218','223','293','296'])).

thf('305',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['303','304'])).

thf('306',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['300','305'])).

thf('307',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('308',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['306','307'])).

thf('309',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['308','309'])).

thf('311',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['310','311'])).

thf('313',plain,(
    $false ),
    inference(demod,[status(thm)],['0','312'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Phc7KAb0zK
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1454 iterations in 0.782s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.25  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.06/1.25  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.06/1.25  thf(sk_E_type, type, sk_E: $i).
% 1.06/1.25  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.06/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.25  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.06/1.25  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.25  thf(sk_G_type, type, sk_G: $i).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.06/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.25  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.06/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.25  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.06/1.25  thf(sk_F_type, type, sk_F: $i).
% 1.06/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.06/1.25  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.06/1.25  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.06/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(t80_tmap_1, conjecture,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25             ( l1_pre_topc @ B ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.25               ( ![D:$i]:
% 1.06/1.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.06/1.25                   ( ![E:$i]:
% 1.06/1.25                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.25                         ( v1_funct_2 @
% 1.06/1.25                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                         ( m1_subset_1 @
% 1.06/1.25                           E @ 
% 1.06/1.25                           ( k1_zfmisc_1 @
% 1.06/1.25                             ( k2_zfmisc_1 @
% 1.06/1.25                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                       ( ![F:$i]:
% 1.06/1.25                         ( ( ( v1_funct_1 @ F ) & 
% 1.06/1.25                             ( v1_funct_2 @
% 1.06/1.25                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                             ( m1_subset_1 @
% 1.06/1.25                               F @ 
% 1.06/1.25                               ( k1_zfmisc_1 @
% 1.06/1.25                                 ( k2_zfmisc_1 @
% 1.06/1.25                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                           ( ![G:$i]:
% 1.06/1.25                             ( ( ( v1_funct_1 @ G ) & 
% 1.06/1.25                                 ( v1_funct_2 @
% 1.06/1.25                                   G @ ( u1_struct_0 @ D ) @ 
% 1.06/1.25                                   ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                                 ( m1_subset_1 @
% 1.06/1.25                                   G @ 
% 1.06/1.25                                   ( k1_zfmisc_1 @
% 1.06/1.25                                     ( k2_zfmisc_1 @
% 1.06/1.25                                       ( u1_struct_0 @ D ) @ 
% 1.06/1.25                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                               ( ( ( ( D ) = ( A ) ) & 
% 1.06/1.25                                   ( r1_funct_2 @
% 1.06/1.25                                     ( u1_struct_0 @ A ) @ 
% 1.06/1.25                                     ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                     ( u1_struct_0 @ D ) @ 
% 1.06/1.25                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.06/1.25                                 ( ( r2_funct_2 @
% 1.06/1.25                                     ( u1_struct_0 @ C ) @ 
% 1.06/1.25                                     ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.06/1.25                                   ( r2_funct_2 @
% 1.06/1.25                                     ( u1_struct_0 @ C ) @ 
% 1.06/1.25                                     ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i]:
% 1.06/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.25            ( l1_pre_topc @ A ) ) =>
% 1.06/1.25          ( ![B:$i]:
% 1.06/1.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25                ( l1_pre_topc @ B ) ) =>
% 1.06/1.25              ( ![C:$i]:
% 1.06/1.25                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.25                  ( ![D:$i]:
% 1.06/1.25                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.06/1.25                      ( ![E:$i]:
% 1.06/1.25                        ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.25                            ( v1_funct_2 @
% 1.06/1.25                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                            ( m1_subset_1 @
% 1.06/1.25                              E @ 
% 1.06/1.25                              ( k1_zfmisc_1 @
% 1.06/1.25                                ( k2_zfmisc_1 @
% 1.06/1.25                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                          ( ![F:$i]:
% 1.06/1.25                            ( ( ( v1_funct_1 @ F ) & 
% 1.06/1.25                                ( v1_funct_2 @
% 1.06/1.25                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                                ( m1_subset_1 @
% 1.06/1.25                                  F @ 
% 1.06/1.25                                  ( k1_zfmisc_1 @
% 1.06/1.25                                    ( k2_zfmisc_1 @
% 1.06/1.25                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                              ( ![G:$i]:
% 1.06/1.25                                ( ( ( v1_funct_1 @ G ) & 
% 1.06/1.25                                    ( v1_funct_2 @
% 1.06/1.25                                      G @ ( u1_struct_0 @ D ) @ 
% 1.06/1.25                                      ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                                    ( m1_subset_1 @
% 1.06/1.25                                      G @ 
% 1.06/1.25                                      ( k1_zfmisc_1 @
% 1.06/1.25                                        ( k2_zfmisc_1 @
% 1.06/1.25                                          ( u1_struct_0 @ D ) @ 
% 1.06/1.25                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                                  ( ( ( ( D ) = ( A ) ) & 
% 1.06/1.25                                      ( r1_funct_2 @
% 1.06/1.25                                        ( u1_struct_0 @ A ) @ 
% 1.06/1.25                                        ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                        ( u1_struct_0 @ D ) @ 
% 1.06/1.25                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.06/1.25                                    ( ( r2_funct_2 @
% 1.06/1.25                                        ( u1_struct_0 @ C ) @ 
% 1.06/1.25                                        ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.06/1.25                                      ( r2_funct_2 @
% 1.06/1.25                                        ( u1_struct_0 @ C ) @ 
% 1.06/1.25                                        ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.06/1.25  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('2', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('5', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.25  thf('7', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('8', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(d4_tmap_1, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25             ( l1_pre_topc @ B ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.25                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                 ( m1_subset_1 @
% 1.06/1.25                   C @ 
% 1.06/1.25                   ( k1_zfmisc_1 @
% 1.06/1.25                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25               ( ![D:$i]:
% 1.06/1.25                 ( ( m1_pre_topc @ D @ A ) =>
% 1.06/1.25                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.06/1.25                     ( k2_partfun1 @
% 1.06/1.25                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.06/1.25                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.06/1.25         ((v2_struct_0 @ X26)
% 1.06/1.25          | ~ (v2_pre_topc @ X26)
% 1.06/1.25          | ~ (l1_pre_topc @ X26)
% 1.06/1.25          | ~ (m1_pre_topc @ X27 @ X28)
% 1.06/1.25          | ((k2_tmap_1 @ X28 @ X26 @ X29 @ X27)
% 1.06/1.25              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ 
% 1.06/1.25                 X29 @ (u1_struct_0 @ X27)))
% 1.06/1.25          | ~ (m1_subset_1 @ X29 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 1.06/1.25          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 1.06/1.25          | ~ (v1_funct_1 @ X29)
% 1.06/1.25          | ~ (l1_pre_topc @ X28)
% 1.06/1.25          | ~ (v2_pre_topc @ X28)
% 1.06/1.25          | (v2_struct_0 @ X28))),
% 1.06/1.25      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v2_struct_0 @ sk_D)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.06/1.25              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25                 sk_E @ (u1_struct_0 @ X0)))
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.25  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('13', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('14', plain, ((v2_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('16', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('20', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('21', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('22', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(redefinition_k2_partfun1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.25       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.06/1.25          | ~ (v1_funct_1 @ X8)
% 1.06/1.25          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.06/1.25  thf('24', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.06/1.25            X0) = (k7_relat_1 @ sk_E @ X0))
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E))),
% 1.06/1.25      inference('sup-', [status(thm)], ['22', '23'])).
% 1.06/1.25  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.06/1.25           X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.25  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('28', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v2_struct_0 @ sk_D)
% 1.06/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.06/1.25              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)],
% 1.06/1.25                ['11', '14', '17', '18', '21', '26', '27', '28'])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.06/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['6', '29'])).
% 1.06/1.25  thf('31', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(cc2_relset_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.25       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.06/1.25  thf('32', plain,
% 1.06/1.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.06/1.25         ((v4_relat_1 @ X5 @ X6)
% 1.06/1.25          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.06/1.25      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.06/1.25  thf('33', plain, ((v4_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.25  thf(t209_relat_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.06/1.25       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (((X0) = (k7_relat_1 @ X0 @ X1))
% 1.06/1.25          | ~ (v4_relat_1 @ X0 @ X1)
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.06/1.25  thf('35', plain,
% 1.06/1.25      ((~ (v1_relat_1 @ sk_E)
% 1.06/1.25        | ((sk_E) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.25  thf('36', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(cc1_relset_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.25       ( v1_relat_1 @ C ) ))).
% 1.06/1.25  thf('37', plain,
% 1.06/1.25      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.25         ((v1_relat_1 @ X2)
% 1.06/1.25          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.06/1.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.06/1.25  thf('38', plain, ((v1_relat_1 @ sk_E)),
% 1.06/1.25      inference('sup-', [status(thm)], ['36', '37'])).
% 1.06/1.25  thf('39', plain, (((sk_E) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))),
% 1.06/1.25      inference('demod', [status(thm)], ['35', '38'])).
% 1.06/1.25  thf('40', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('demod', [status(thm)], ['30', '39'])).
% 1.06/1.25  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('42', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_D)
% 1.06/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E)))),
% 1.06/1.25      inference('clc', [status(thm)], ['40', '41'])).
% 1.06/1.25  thf('43', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('44', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.06/1.25      inference('clc', [status(thm)], ['42', '43'])).
% 1.06/1.25  thf('45', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(dt_k2_tmap_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.06/1.25         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25         ( m1_subset_1 @
% 1.06/1.25           C @ 
% 1.06/1.25           ( k1_zfmisc_1 @
% 1.06/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.06/1.25         ( l1_struct_0 @ D ) ) =>
% 1.06/1.25       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.06/1.25         ( v1_funct_2 @
% 1.06/1.25           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.06/1.25           ( u1_struct_0 @ B ) ) & 
% 1.06/1.25         ( m1_subset_1 @
% 1.06/1.25           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.25           ( k1_zfmisc_1 @
% 1.06/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.06/1.25  thf('46', plain,
% 1.06/1.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X30 @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 1.06/1.25          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 1.06/1.25          | ~ (v1_funct_1 @ X30)
% 1.06/1.25          | ~ (l1_struct_0 @ X32)
% 1.06/1.25          | ~ (l1_struct_0 @ X31)
% 1.06/1.25          | ~ (l1_struct_0 @ X33)
% 1.06/1.25          | (m1_subset_1 @ (k2_tmap_1 @ X31 @ X32 @ X30 @ X33) @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.25  thf('47', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (l1_struct_0 @ X0)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_D)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_B)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['45', '46'])).
% 1.06/1.25  thf('48', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf(dt_l1_pre_topc, axiom,
% 1.06/1.25    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.25  thf('49', plain,
% 1.06/1.25      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.25  thf('50', plain, ((l1_struct_0 @ sk_D)),
% 1.06/1.25      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.25  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('52', plain,
% 1.06/1.25      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.25  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.25      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.25  thf('54', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('55', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('56', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (l1_struct_0 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['47', '50', '53', '54', '55'])).
% 1.06/1.25  thf(t77_tmap_1, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25             ( l1_pre_topc @ B ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.25               ( ![D:$i]:
% 1.06/1.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.06/1.25                   ( ![E:$i]:
% 1.06/1.25                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.25                         ( v1_funct_2 @
% 1.06/1.25                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                         ( m1_subset_1 @
% 1.06/1.25                           E @ 
% 1.06/1.25                           ( k1_zfmisc_1 @
% 1.06/1.25                             ( k2_zfmisc_1 @
% 1.06/1.25                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                       ( ![F:$i]:
% 1.06/1.25                         ( ( ( v1_funct_1 @ F ) & 
% 1.06/1.25                             ( v1_funct_2 @
% 1.06/1.25                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                             ( m1_subset_1 @
% 1.06/1.25                               F @ 
% 1.06/1.25                               ( k1_zfmisc_1 @
% 1.06/1.25                                 ( k2_zfmisc_1 @
% 1.06/1.25                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                           ( ( ( r2_funct_2 @
% 1.06/1.25                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.06/1.25                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 1.06/1.25                               ( m1_pre_topc @ D @ C ) ) =>
% 1.06/1.25                             ( r2_funct_2 @
% 1.06/1.25                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 1.06/1.25                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf('57', plain,
% 1.06/1.25      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.06/1.25         ((v2_struct_0 @ X39)
% 1.06/1.25          | ~ (v2_pre_topc @ X39)
% 1.06/1.25          | ~ (l1_pre_topc @ X39)
% 1.06/1.25          | (v2_struct_0 @ X40)
% 1.06/1.25          | ~ (m1_pre_topc @ X40 @ X41)
% 1.06/1.25          | ~ (v1_funct_1 @ X42)
% 1.06/1.25          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X39))
% 1.06/1.25          | ~ (m1_subset_1 @ X42 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X39))))
% 1.06/1.25          | (r2_funct_2 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ 
% 1.06/1.25             (k3_tmap_1 @ X41 @ X39 @ X43 @ X40 @ X42) @ 
% 1.06/1.25             (k2_tmap_1 @ X41 @ X39 @ X44 @ X40))
% 1.06/1.25          | ~ (r2_funct_2 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X39) @ X42 @ 
% 1.06/1.25               (k2_tmap_1 @ X41 @ X39 @ X44 @ X43))
% 1.06/1.25          | ~ (m1_pre_topc @ X40 @ X43)
% 1.06/1.25          | ~ (m1_subset_1 @ X44 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 1.06/1.25          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 1.06/1.25          | ~ (v1_funct_1 @ X44)
% 1.06/1.25          | ~ (m1_pre_topc @ X43 @ X41)
% 1.06/1.25          | (v2_struct_0 @ X43)
% 1.06/1.25          | ~ (l1_pre_topc @ X41)
% 1.06/1.25          | ~ (v2_pre_topc @ X41)
% 1.06/1.25          | (v2_struct_0 @ X41))),
% 1.06/1.25      inference('cnf', [status(esa)], [t77_tmap_1])).
% 1.06/1.25  thf('58', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         (~ (l1_struct_0 @ X0)
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ X0)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ X2)
% 1.06/1.25          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (m1_pre_topc @ X3 @ X0)
% 1.06/1.25          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 1.06/1.25          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 1.06/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.06/1.25             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 1.06/1.25          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (m1_pre_topc @ X3 @ X1)
% 1.06/1.25          | (v2_struct_0 @ X3)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('sup-', [status(thm)], ['56', '57'])).
% 1.06/1.25  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('60', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('61', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         (~ (l1_struct_0 @ X0)
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ X0)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ X2)
% 1.06/1.25          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (m1_subset_1 @ X2 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (m1_pre_topc @ X3 @ X0)
% 1.06/1.25          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 1.06/1.25          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 1.06/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.06/1.25             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 1.06/1.25          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (m1_pre_topc @ X3 @ X1)
% 1.06/1.25          | (v2_struct_0 @ X3)
% 1.06/1.25          | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.06/1.25  thf('62', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) @ sk_E)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ X0)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D))
% 1.06/1.25          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) @ 
% 1.06/1.25               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 1.06/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)) @ 
% 1.06/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | ~ (m1_subset_1 @ sk_E @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['44', '61'])).
% 1.06/1.25  thf('63', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.06/1.25      inference('clc', [status(thm)], ['42', '43'])).
% 1.06/1.25  thf('64', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(redefinition_r2_funct_2, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.25         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.06/1.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.25       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.06/1.25  thf('65', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.06/1.25          | ~ (v1_funct_1 @ X12)
% 1.06/1.25          | ~ (v1_funct_1 @ X15)
% 1.06/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.06/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | (r2_funct_2 @ X13 @ X14 @ X12 @ X15)
% 1.06/1.25          | ((X12) != (X15)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.25  thf('66', plain,
% 1.06/1.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.25         ((r2_funct_2 @ X13 @ X14 @ X15 @ X15)
% 1.06/1.25          | ~ (v1_funct_1 @ X15)
% 1.06/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.06/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.06/1.25      inference('simplify', [status(thm)], ['65'])).
% 1.06/1.25  thf('67', plain,
% 1.06/1.25      ((~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.06/1.25           sk_E))),
% 1.06/1.25      inference('sup-', [status(thm)], ['64', '66'])).
% 1.06/1.25  thf('68', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('70', plain,
% 1.06/1.25      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)),
% 1.06/1.25      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.06/1.25  thf('71', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.06/1.25      inference('clc', [status(thm)], ['42', '43'])).
% 1.06/1.25  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('73', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.06/1.25      inference('clc', [status(thm)], ['42', '43'])).
% 1.06/1.25  thf('74', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('75', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.06/1.25      inference('clc', [status(thm)], ['42', '43'])).
% 1.06/1.25  thf('76', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf('77', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('78', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.25  thf('80', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('81', plain, ((v2_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('82', plain, ((l1_struct_0 @ sk_D)),
% 1.06/1.25      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.25  thf('83', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v2_struct_0 @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ X0)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('demod', [status(thm)],
% 1.06/1.25                ['62', '63', '70', '71', '72', '73', '74', '75', '76', '77', 
% 1.06/1.25                 '78', '79', '80', '81', '82'])).
% 1.06/1.25  thf('84', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v2_struct_0 @ sk_D)
% 1.06/1.25          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ X0)
% 1.06/1.25          | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('simplify', [status(thm)], ['83'])).
% 1.06/1.25  thf('85', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['3', '84'])).
% 1.06/1.25  thf('86', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('87', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v2_struct_0 @ sk_D)
% 1.06/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.06/1.25              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)],
% 1.06/1.25                ['11', '14', '17', '18', '21', '26', '27', '28'])).
% 1.06/1.25  thf('88', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['86', '87'])).
% 1.06/1.25  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('90', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_D)
% 1.06/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.06/1.25      inference('clc', [status(thm)], ['88', '89'])).
% 1.06/1.25  thf('91', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('92', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('93', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('demod', [status(thm)], ['85', '92'])).
% 1.06/1.25  thf('94', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.25  thf('96', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(dt_k3_tmap_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.25         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.06/1.25         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.06/1.25         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.06/1.25         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25         ( m1_subset_1 @
% 1.06/1.25           E @ 
% 1.06/1.25           ( k1_zfmisc_1 @
% 1.06/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.06/1.25         ( v1_funct_2 @
% 1.06/1.25           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.06/1.25           ( u1_struct_0 @ B ) ) & 
% 1.06/1.25         ( m1_subset_1 @
% 1.06/1.25           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.06/1.25           ( k1_zfmisc_1 @
% 1.06/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.06/1.25  thf('97', plain,
% 1.06/1.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X34 @ X35)
% 1.06/1.25          | ~ (m1_pre_topc @ X36 @ X35)
% 1.06/1.25          | ~ (l1_pre_topc @ X37)
% 1.06/1.25          | ~ (v2_pre_topc @ X37)
% 1.06/1.25          | (v2_struct_0 @ X37)
% 1.06/1.25          | ~ (l1_pre_topc @ X35)
% 1.06/1.25          | ~ (v2_pre_topc @ X35)
% 1.06/1.25          | (v2_struct_0 @ X35)
% 1.06/1.25          | ~ (v1_funct_1 @ X38)
% 1.06/1.25          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))
% 1.06/1.25          | ~ (m1_subset_1 @ X38 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))))
% 1.06/1.25          | (m1_subset_1 @ (k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38) @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.06/1.25  thf('98', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['96', '97'])).
% 1.06/1.25  thf('99', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('100', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('101', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('103', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.06/1.25      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 1.06/1.25  thf('104', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['95', '103'])).
% 1.06/1.25  thf('105', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('106', plain, ((v2_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('107', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.06/1.25  thf('108', plain,
% 1.06/1.25      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | (v2_struct_0 @ sk_D)
% 1.06/1.25        | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('sup-', [status(thm)], ['94', '107'])).
% 1.06/1.25  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('110', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('clc', [status(thm)], ['108', '109'])).
% 1.06/1.25  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('112', plain,
% 1.06/1.25      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('clc', [status(thm)], ['110', '111'])).
% 1.06/1.25  thf('113', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.06/1.25          | ~ (v1_funct_1 @ X12)
% 1.06/1.25          | ~ (v1_funct_1 @ X15)
% 1.06/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.06/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ((X12) = (X15))
% 1.06/1.25          | ~ (r2_funct_2 @ X13 @ X14 @ X12 @ X15))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.25  thf('114', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.06/1.25          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ X0)
% 1.06/1.25          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.06/1.25          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['112', '113'])).
% 1.06/1.25  thf('115', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('116', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.25  thf('117', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf('118', plain,
% 1.06/1.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X34 @ X35)
% 1.06/1.25          | ~ (m1_pre_topc @ X36 @ X35)
% 1.06/1.25          | ~ (l1_pre_topc @ X37)
% 1.06/1.25          | ~ (v2_pre_topc @ X37)
% 1.06/1.25          | (v2_struct_0 @ X37)
% 1.06/1.25          | ~ (l1_pre_topc @ X35)
% 1.06/1.25          | ~ (v2_pre_topc @ X35)
% 1.06/1.25          | (v2_struct_0 @ X35)
% 1.06/1.25          | ~ (v1_funct_1 @ X38)
% 1.06/1.25          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))
% 1.06/1.25          | ~ (m1_subset_1 @ X38 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))))
% 1.06/1.25          | (v1_funct_1 @ (k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.06/1.25  thf('119', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['117', '118'])).
% 1.06/1.25  thf('120', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('121', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('122', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('124', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.06/1.25      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 1.06/1.25  thf('125', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['116', '124'])).
% 1.06/1.25  thf('126', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('127', plain, ((v2_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('128', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.06/1.25      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.06/1.25  thf('129', plain,
% 1.06/1.25      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.06/1.25        | (v2_struct_0 @ sk_D)
% 1.06/1.25        | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('sup-', [status(thm)], ['115', '128'])).
% 1.06/1.25  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('131', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)))),
% 1.06/1.25      inference('clc', [status(thm)], ['129', '130'])).
% 1.06/1.25  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('133', plain,
% 1.06/1.25      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 1.06/1.25      inference('clc', [status(thm)], ['131', '132'])).
% 1.06/1.25  thf('134', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('135', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.25  thf('136', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf('137', plain,
% 1.06/1.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X34 @ X35)
% 1.06/1.25          | ~ (m1_pre_topc @ X36 @ X35)
% 1.06/1.25          | ~ (l1_pre_topc @ X37)
% 1.06/1.25          | ~ (v2_pre_topc @ X37)
% 1.06/1.25          | (v2_struct_0 @ X37)
% 1.06/1.25          | ~ (l1_pre_topc @ X35)
% 1.06/1.25          | ~ (v2_pre_topc @ X35)
% 1.06/1.25          | (v2_struct_0 @ X35)
% 1.06/1.25          | ~ (v1_funct_1 @ X38)
% 1.06/1.25          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))
% 1.06/1.25          | ~ (m1_subset_1 @ X38 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))))
% 1.06/1.25          | (v1_funct_2 @ (k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38) @ 
% 1.06/1.25             (u1_struct_0 @ X34) @ (u1_struct_0 @ X37)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.06/1.25  thf('138', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['136', '137'])).
% 1.06/1.25  thf('139', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('140', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('141', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('143', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (v2_pre_topc @ X1)
% 1.06/1.25          | ~ (l1_pre_topc @ X1)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.06/1.25      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 1.06/1.25  thf('144', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.06/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['135', '143'])).
% 1.06/1.25  thf('145', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('146', plain, ((v2_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf('147', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.06/1.25          | (v2_struct_0 @ sk_B)
% 1.06/1.25          | (v2_struct_0 @ sk_D)
% 1.06/1.25          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.06/1.25             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('demod', [status(thm)], ['144', '145', '146'])).
% 1.06/1.25  thf('148', plain,
% 1.06/1.25      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (v2_struct_0 @ sk_D)
% 1.06/1.25        | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('sup-', [status(thm)], ['134', '147'])).
% 1.06/1.25  thf('149', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('150', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('clc', [status(thm)], ['148', '149'])).
% 1.06/1.25  thf('151', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('152', plain,
% 1.06/1.25      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('clc', [status(thm)], ['150', '151'])).
% 1.06/1.25  thf('153', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.06/1.25          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['114', '133', '152'])).
% 1.06/1.25  thf('154', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_D)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (v2_struct_0 @ sk_B)
% 1.06/1.25        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.06/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['93', '153'])).
% 1.06/1.25  thf('155', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('156', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf('157', plain,
% 1.06/1.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X30 @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 1.06/1.25          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 1.06/1.25          | ~ (v1_funct_1 @ X30)
% 1.06/1.25          | ~ (l1_struct_0 @ X32)
% 1.06/1.25          | ~ (l1_struct_0 @ X31)
% 1.06/1.25          | ~ (l1_struct_0 @ X33)
% 1.06/1.25          | (v1_funct_1 @ (k2_tmap_1 @ X31 @ X32 @ X30 @ X33)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.25  thf('158', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (l1_struct_0 @ X0)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_D)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_B)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['156', '157'])).
% 1.06/1.25  thf('159', plain, ((l1_struct_0 @ sk_D)),
% 1.06/1.25      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.25  thf('160', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.25      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.25  thf('161', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('162', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('163', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (l1_struct_0 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['158', '159', '160', '161', '162'])).
% 1.06/1.25  thf('164', plain,
% 1.06/1.25      (((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ~ (l1_struct_0 @ sk_C))),
% 1.06/1.25      inference('sup+', [status(thm)], ['155', '163'])).
% 1.06/1.25  thf('165', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf(dt_m1_pre_topc, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( l1_pre_topc @ A ) =>
% 1.06/1.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.06/1.25  thf('166', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X17 @ X18)
% 1.06/1.25          | (l1_pre_topc @ X17)
% 1.06/1.25          | ~ (l1_pre_topc @ X18))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.06/1.25  thf('167', plain, ((~ (l1_pre_topc @ sk_D) | (l1_pre_topc @ sk_C))),
% 1.06/1.25      inference('sup-', [status(thm)], ['165', '166'])).
% 1.06/1.25  thf('168', plain, ((l1_pre_topc @ sk_D)),
% 1.06/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('169', plain, ((l1_pre_topc @ sk_C)),
% 1.06/1.25      inference('demod', [status(thm)], ['167', '168'])).
% 1.06/1.25  thf('170', plain,
% 1.06/1.25      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.25  thf('171', plain, ((l1_struct_0 @ sk_C)),
% 1.06/1.25      inference('sup-', [status(thm)], ['169', '170'])).
% 1.06/1.25  thf('172', plain,
% 1.06/1.25      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('demod', [status(thm)], ['164', '171'])).
% 1.06/1.25  thf('173', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('174', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf('175', plain,
% 1.06/1.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X30 @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 1.06/1.25          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 1.06/1.25          | ~ (v1_funct_1 @ X30)
% 1.06/1.25          | ~ (l1_struct_0 @ X32)
% 1.06/1.25          | ~ (l1_struct_0 @ X31)
% 1.06/1.25          | ~ (l1_struct_0 @ X33)
% 1.06/1.25          | (v1_funct_2 @ (k2_tmap_1 @ X31 @ X32 @ X30 @ X33) @ 
% 1.06/1.25             (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.25  thf('176', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (l1_struct_0 @ X0)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_D)
% 1.06/1.25          | ~ (l1_struct_0 @ sk_B)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['174', '175'])).
% 1.06/1.25  thf('177', plain, ((l1_struct_0 @ sk_D)),
% 1.06/1.25      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.25  thf('178', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.25      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.25  thf('179', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('180', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('181', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (l1_struct_0 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 1.06/1.25  thf('182', plain,
% 1.06/1.25      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ~ (l1_struct_0 @ sk_C))),
% 1.06/1.25      inference('sup+', [status(thm)], ['173', '181'])).
% 1.06/1.25  thf('183', plain, ((l1_struct_0 @ sk_C)),
% 1.06/1.25      inference('sup-', [status(thm)], ['169', '170'])).
% 1.06/1.25  thf('184', plain,
% 1.06/1.25      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['182', '183'])).
% 1.06/1.25  thf('185', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('186', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (l1_struct_0 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['47', '50', '53', '54', '55'])).
% 1.06/1.25  thf('187', plain,
% 1.06/1.25      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | ~ (l1_struct_0 @ sk_C))),
% 1.06/1.25      inference('sup+', [status(thm)], ['185', '186'])).
% 1.06/1.25  thf('188', plain, ((l1_struct_0 @ sk_C)),
% 1.06/1.25      inference('sup-', [status(thm)], ['169', '170'])).
% 1.06/1.25  thf('189', plain,
% 1.06/1.25      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['187', '188'])).
% 1.06/1.25  thf('190', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_D)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (v2_struct_0 @ sk_B)
% 1.06/1.25        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.06/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.06/1.25      inference('demod', [status(thm)], ['154', '172', '184', '189'])).
% 1.06/1.25  thf('191', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('192', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.06/1.25      inference('split', [status(esa)], ['191'])).
% 1.06/1.25  thf('193', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('194', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['192', '193'])).
% 1.06/1.25  thf('195', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (l1_struct_0 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['47', '50', '53', '54', '55'])).
% 1.06/1.25  thf('196', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.06/1.25          | ~ (v1_funct_1 @ X12)
% 1.06/1.25          | ~ (v1_funct_1 @ X15)
% 1.06/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.06/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ((X12) = (X15))
% 1.06/1.25          | ~ (r2_funct_2 @ X13 @ X14 @ X12 @ X15))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.25  thf('197', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (~ (l1_struct_0 @ X0)
% 1.06/1.25          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 1.06/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) = (X1))
% 1.06/1.25          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.06/1.25          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['195', '196'])).
% 1.06/1.25  thf('198', plain,
% 1.06/1.25      (((~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.06/1.25            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.06/1.25         | ~ (v1_funct_1 @ sk_F)
% 1.06/1.25         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25         | ~ (m1_subset_1 @ sk_F @ 
% 1.06/1.25              (k1_zfmisc_1 @ 
% 1.06/1.25               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25         | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) = (sk_F))
% 1.06/1.25         | ~ (l1_struct_0 @ sk_C)))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['194', '197'])).
% 1.06/1.25  thf('199', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('200', plain,
% 1.06/1.25      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['182', '183'])).
% 1.06/1.25  thf('201', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('202', plain,
% 1.06/1.25      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('demod', [status(thm)], ['164', '171'])).
% 1.06/1.25  thf('203', plain, ((v1_funct_1 @ sk_F)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('204', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('205', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_F @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('206', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('207', plain, ((l1_struct_0 @ sk_C)),
% 1.06/1.25      inference('sup-', [status(thm)], ['169', '170'])).
% 1.06/1.25  thf('208', plain,
% 1.06/1.25      ((((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F)))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)],
% 1.06/1.25                ['198', '199', '200', '201', '202', '203', '204', '205', 
% 1.06/1.25                 '206', '207'])).
% 1.06/1.25  thf('209', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('210', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('211', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('212', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.06/1.25  thf('213', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('split', [status(esa)], ['212'])).
% 1.06/1.25  thf('214', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('215', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('split', [status(esa)], ['214'])).
% 1.06/1.25  thf('216', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('217', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['215', '216'])).
% 1.06/1.25  thf('218', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('sup-', [status(thm)], ['213', '217'])).
% 1.06/1.25  thf('219', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('220', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('221', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('222', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('demod', [status(thm)], ['219', '220', '221'])).
% 1.06/1.25  thf('223', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.06/1.25       ~
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.06/1.25      inference('split', [status(esa)], ['222'])).
% 1.06/1.25  thf('224', plain,
% 1.06/1.25      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('225', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('226', plain,
% 1.06/1.25      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.06/1.25      inference('demod', [status(thm)], ['224', '225'])).
% 1.06/1.25  thf('227', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_E @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.25  thf(redefinition_r1_funct_2, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.06/1.25     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.06/1.25         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.06/1.25         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.25         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.06/1.25         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.06/1.25       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.06/1.25  thf('228', plain,
% 1.06/1.25      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.06/1.25          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 1.06/1.25          | ~ (v1_funct_1 @ X20)
% 1.06/1.25          | (v1_xboole_0 @ X23)
% 1.06/1.25          | (v1_xboole_0 @ X22)
% 1.06/1.25          | ~ (v1_funct_1 @ X24)
% 1.06/1.25          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 1.06/1.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 1.06/1.25          | ((X20) = (X24))
% 1.06/1.25          | ~ (r1_funct_2 @ X21 @ X22 @ X25 @ X23 @ X20 @ X24))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.06/1.25  thf('229', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.06/1.25             X1 @ sk_E @ X0)
% 1.06/1.25          | ((sk_E) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ X0)
% 1.06/1.25          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | (v1_xboole_0 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['227', '228'])).
% 1.06/1.25  thf('230', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('231', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.25  thf('232', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.06/1.25             X1 @ sk_E @ X0)
% 1.06/1.25          | ((sk_E) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.06/1.25          | ~ (v1_funct_1 @ X0)
% 1.06/1.25          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | (v1_xboole_0 @ X1))),
% 1.06/1.25      inference('demod', [status(thm)], ['229', '230', '231'])).
% 1.06/1.25  thf('233', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ~ (v1_funct_1 @ sk_G)
% 1.06/1.25        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ~ (m1_subset_1 @ sk_G @ 
% 1.06/1.25             (k1_zfmisc_1 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | ((sk_E) = (sk_G)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['226', '232'])).
% 1.06/1.25  thf('234', plain, ((v1_funct_1 @ sk_G)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('235', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('236', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_G @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('237', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ((sk_E) = (sk_G)))),
% 1.06/1.25      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 1.06/1.25  thf('238', plain,
% 1.06/1.25      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['237'])).
% 1.06/1.25  thf(fc2_struct_0, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.06/1.25       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.25  thf('239', plain,
% 1.06/1.25      (![X19 : $i]:
% 1.06/1.25         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 1.06/1.25          | ~ (l1_struct_0 @ X19)
% 1.06/1.25          | (v2_struct_0 @ X19))),
% 1.06/1.25      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.06/1.25  thf('240', plain,
% 1.06/1.25      ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 1.06/1.25      inference('sup-', [status(thm)], ['238', '239'])).
% 1.06/1.25  thf('241', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.25      inference('sup-', [status(thm)], ['51', '52'])).
% 1.06/1.25  thf('242', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['240', '241'])).
% 1.06/1.25  thf('243', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('244', plain, (((sk_E) = (sk_G))),
% 1.06/1.25      inference('clc', [status(thm)], ['242', '243'])).
% 1.06/1.25  thf('245', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('split', [status(esa)], ['191'])).
% 1.06/1.25  thf('246', plain, (((sk_D) = (sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('247', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['245', '246'])).
% 1.06/1.25  thf('248', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['244', '247'])).
% 1.06/1.25  thf('249', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.06/1.25          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['114', '133', '152'])).
% 1.06/1.25  thf('250', plain,
% 1.06/1.25      (((~ (v1_funct_1 @ sk_F)
% 1.06/1.25         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25         | ~ (m1_subset_1 @ sk_F @ 
% 1.06/1.25              (k1_zfmisc_1 @ 
% 1.06/1.25               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25         | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F))))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['248', '249'])).
% 1.06/1.25  thf('251', plain, ((v1_funct_1 @ sk_F)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('252', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('253', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_F @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('254', plain,
% 1.06/1.25      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['250', '251', '252', '253'])).
% 1.06/1.25  thf('255', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.06/1.25           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('demod', [status(thm)], ['85', '92'])).
% 1.06/1.25  thf('256', plain,
% 1.06/1.25      ((((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25          (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25         | (v2_struct_0 @ sk_D)
% 1.06/1.25         | (v2_struct_0 @ sk_C)
% 1.06/1.25         | (v2_struct_0 @ sk_B)))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['254', '255'])).
% 1.06/1.25  thf('257', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (l1_struct_0 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['47', '50', '53', '54', '55'])).
% 1.06/1.25  thf('258', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_F @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('259', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.06/1.25          | ~ (v1_funct_1 @ X12)
% 1.06/1.25          | ~ (v1_funct_1 @ X15)
% 1.06/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.06/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.06/1.25          | ((X12) = (X15))
% 1.06/1.25          | ~ (r2_funct_2 @ X13 @ X14 @ X12 @ X15))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.25  thf('260', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             X0)
% 1.06/1.25          | ((sk_F) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ X0)
% 1.06/1.25          | ~ (v1_funct_1 @ sk_F)
% 1.06/1.25          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['258', '259'])).
% 1.06/1.25  thf('261', plain, ((v1_funct_1 @ sk_F)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('262', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('263', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             X0)
% 1.06/1.25          | ((sk_F) = (X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25          | ~ (v1_funct_1 @ X0))),
% 1.06/1.25      inference('demod', [status(thm)], ['260', '261', '262'])).
% 1.06/1.25  thf('264', plain,
% 1.06/1.25      ((~ (l1_struct_0 @ sk_C)
% 1.06/1.25        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.06/1.25        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.06/1.25             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ((sk_F) = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['257', '263'])).
% 1.06/1.25  thf('265', plain, ((l1_struct_0 @ sk_C)),
% 1.06/1.25      inference('sup-', [status(thm)], ['169', '170'])).
% 1.06/1.25  thf('266', plain,
% 1.06/1.25      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.06/1.25        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.06/1.25             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ((sk_F) = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 1.06/1.25      inference('demod', [status(thm)], ['264', '265'])).
% 1.06/1.25  thf('267', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('268', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('269', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('270', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('271', plain,
% 1.06/1.25      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.06/1.25      inference('demod', [status(thm)], ['266', '267', '268', '269', '270'])).
% 1.06/1.25  thf('272', plain,
% 1.06/1.25      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.06/1.25        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('demod', [status(thm)], ['182', '183'])).
% 1.06/1.25  thf('273', plain,
% 1.06/1.25      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.06/1.25      inference('demod', [status(thm)], ['271', '272'])).
% 1.06/1.25  thf('274', plain,
% 1.06/1.25      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('demod', [status(thm)], ['164', '171'])).
% 1.06/1.25  thf('275', plain,
% 1.06/1.25      ((((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.06/1.25        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.06/1.25      inference('demod', [status(thm)], ['273', '274'])).
% 1.06/1.25  thf('276', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_B)
% 1.06/1.25         | (v2_struct_0 @ sk_C)
% 1.06/1.25         | (v2_struct_0 @ sk_D)
% 1.06/1.25         | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['256', '275'])).
% 1.06/1.25  thf('277', plain,
% 1.06/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.06/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('278', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.06/1.25      inference('split', [status(esa)], ['222'])).
% 1.06/1.25  thf('279', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['277', '278'])).
% 1.06/1.25  thf('280', plain,
% 1.06/1.25      (((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25            sk_F)
% 1.06/1.25         | (v2_struct_0 @ sk_D)
% 1.06/1.25         | (v2_struct_0 @ sk_C)
% 1.06/1.25         | (v2_struct_0 @ sk_B)))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['276', '279'])).
% 1.06/1.25  thf('281', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_F @ 
% 1.06/1.25        (k1_zfmisc_1 @ 
% 1.06/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('282', plain,
% 1.06/1.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.25         ((r2_funct_2 @ X13 @ X14 @ X15 @ X15)
% 1.06/1.25          | ~ (v1_funct_1 @ X15)
% 1.06/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.06/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.06/1.25      inference('simplify', [status(thm)], ['65'])).
% 1.06/1.25  thf('283', plain,
% 1.06/1.25      ((~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | ~ (v1_funct_1 @ sk_F)
% 1.06/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25           sk_F))),
% 1.06/1.25      inference('sup-', [status(thm)], ['281', '282'])).
% 1.06/1.25  thf('284', plain,
% 1.06/1.25      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('285', plain, ((v1_funct_1 @ sk_F)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('286', plain,
% 1.06/1.25      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.06/1.25      inference('demod', [status(thm)], ['283', '284', '285'])).
% 1.06/1.25  thf('287', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['280', '286'])).
% 1.06/1.25  thf('288', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('289', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('clc', [status(thm)], ['287', '288'])).
% 1.06/1.25  thf('290', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('291', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_C))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('clc', [status(thm)], ['289', '290'])).
% 1.06/1.25  thf('292', plain, (~ (v2_struct_0 @ sk_C)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('293', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.06/1.25      inference('sup-', [status(thm)], ['291', '292'])).
% 1.06/1.25  thf('294', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['245', '246'])).
% 1.06/1.25  thf('295', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('split', [status(esa)], ['222'])).
% 1.06/1.25  thf('296', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('sup-', [status(thm)], ['294', '295'])).
% 1.06/1.25  thf('297', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('split', [status(esa)], ['191'])).
% 1.06/1.25  thf('298', plain,
% 1.06/1.25      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.06/1.25      inference('sat_resolution*', [status(thm)],
% 1.06/1.25                ['218', '223', '293', '296', '297'])).
% 1.06/1.25  thf('299', plain, (((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F))),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['208', '298'])).
% 1.06/1.25  thf('300', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_D)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (v2_struct_0 @ sk_B)
% 1.06/1.25        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['190', '299'])).
% 1.06/1.25  thf('301', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['215', '216'])).
% 1.06/1.25  thf('302', plain, (((sk_E) = (sk_G))),
% 1.06/1.25      inference('clc', [status(thm)], ['242', '243'])).
% 1.06/1.25  thf('303', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.06/1.25      inference('demod', [status(thm)], ['301', '302'])).
% 1.06/1.25  thf('304', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.06/1.25      inference('sat_resolution*', [status(thm)], ['218', '223', '293', '296'])).
% 1.06/1.25  thf('305', plain,
% 1.06/1.25      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.25          (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['303', '304'])).
% 1.06/1.25  thf('306', plain,
% 1.06/1.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.06/1.25           sk_F)
% 1.06/1.25        | (v2_struct_0 @ sk_B)
% 1.06/1.25        | (v2_struct_0 @ sk_C)
% 1.06/1.25        | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['300', '305'])).
% 1.06/1.25  thf('307', plain,
% 1.06/1.25      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.06/1.25      inference('demod', [status(thm)], ['283', '284', '285'])).
% 1.06/1.25  thf('308', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 1.06/1.25      inference('demod', [status(thm)], ['306', '307'])).
% 1.06/1.25  thf('309', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('310', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.06/1.25      inference('clc', [status(thm)], ['308', '309'])).
% 1.06/1.25  thf('311', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('312', plain, ((v2_struct_0 @ sk_C)),
% 1.06/1.25      inference('clc', [status(thm)], ['310', '311'])).
% 1.06/1.25  thf('313', plain, ($false), inference('demod', [status(thm)], ['0', '312'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.06/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
