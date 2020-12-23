%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6gBO6O8VZg

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:09 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  344 (4106 expanded)
%              Number of leaves         :   42 (1157 expanded)
%              Depth                    :   29
%              Number of atoms          : 4363 (229609 expanded)
%              Number of equality atoms :   83 (2694 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
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

thf(t78_tmap_1,axiom,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X40 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X39 ) @ ( k3_tmap_1 @ X41 @ X39 @ X40 @ X42 @ ( k2_tmap_1 @ X41 @ X39 @ X43 @ X40 ) ) @ ( k2_tmap_1 @ X41 @ X39 @ X43 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
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
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14','17','18','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,(
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

thf('28',plain,(
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

thf('29',plain,(
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
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','38','39','40'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v4_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('70',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('71',plain,(
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

thf('72',plain,(
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

thf('73',plain,(
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
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

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

thf('88',plain,(
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

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('91',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('93',plain,(
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

thf('94',plain,(
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
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('96',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('102',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('110',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('111',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('112',plain,(
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

thf('113',plain,(
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
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('115',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('121',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','108','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','128'])).

thf('130',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('131',plain,(
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

thf('132',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X31 @ X32 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('135',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('139',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','136','139','140','141'])).

thf('143',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['130','142'])).

thf('144',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('145',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('148',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','150'])).

thf('152',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('153',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('154',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X31 @ X32 @ X30 @ X33 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('157',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['137','138'])).

thf('158',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['152','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['148','149'])).

thf('163',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('165',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('166',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X31 @ X32 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['137','138'])).

thf('170',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','172'])).

thf('174',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['148','149'])).

thf('175',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['129','151','163','175'])).

thf('177',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['177'])).

thf('179',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('182',plain,(
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

thf('183',plain,(
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
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
        = sk_F )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('186',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('187',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('188',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','150'])).

thf('189',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('193',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['148','149'])).

thf('194',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['184','185','186','187','188','189','190','191','192','193'])).

thf('195',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['198'])).

thf('200',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['200'])).

thf('202',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['199','203'])).

thf('205',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['208'])).

thf('210',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
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

thf('214',plain,(
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

thf('215',plain,(
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
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('218',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['212','218'])).

thf('220',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('225',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('226',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['137','138'])).

thf('228',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['228','229'])).

thf('231',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['177'])).

thf('232',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['230','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','108','127'])).

thf('236',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['67'])).

thf('242',plain,
    ( ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('244',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
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

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 )
      | ( sk_F = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 )
      | ( sk_F = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','249'])).

thf('251',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['148','149'])).

thf('252',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('254',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('255',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('256',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('257',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['252','253','254','255','256'])).

thf('258',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('259',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','150'])).

thf('261',plain,
    ( ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( sk_F
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['242','261'])).

thf('263',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('264',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['208'])).

thf('265',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,
    ( ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['262','265'])).

thf('267',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
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

thf('269',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_funct_2 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,
    ( ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['267','269'])).

thf('271',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['270','271','272'])).

thf('274',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['266','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['276','277'])).

thf('279',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('282',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['208'])).

thf('283',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['177'])).

thf('285',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['204','209','280','283','284'])).

thf('286',plain,
    ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    = sk_F ),
    inference(simpl_trail,[status(thm)],['194','285'])).

thf('287',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F ) ),
    inference(demod,[status(thm)],['176','286'])).

thf('288',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('289',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['228','229'])).

thf('290',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['204','209','280','283'])).

thf('292',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['290','291'])).

thf('293',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['287','292'])).

thf('294',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['270','271','272'])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('298',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['297','298'])).

thf('300',plain,(
    $false ),
    inference(demod,[status(thm)],['0','299'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6gBO6O8VZg
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.07/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.25  % Solved by: fo/fo7.sh
% 1.07/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.25  % done 1533 iterations in 0.778s
% 1.07/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.25  % SZS output start Refutation
% 1.07/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.25  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.25  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.07/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.25  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.07/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.25  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.07/1.25  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.07/1.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.07/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.25  thf(sk_F_type, type, sk_F: $i).
% 1.07/1.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.07/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.25  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.07/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.07/1.25  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.07/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.25  thf(sk_G_type, type, sk_G: $i).
% 1.07/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.25  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.07/1.25  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.07/1.25  thf(sk_E_type, type, sk_E: $i).
% 1.07/1.25  thf(t80_tmap_1, conjecture,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.25       ( ![B:$i]:
% 1.07/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.07/1.25             ( l1_pre_topc @ B ) ) =>
% 1.07/1.25           ( ![C:$i]:
% 1.07/1.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.07/1.25               ( ![D:$i]:
% 1.07/1.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.07/1.25                   ( ![E:$i]:
% 1.07/1.25                     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.25                         ( v1_funct_2 @
% 1.07/1.25                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                         ( m1_subset_1 @
% 1.07/1.25                           E @ 
% 1.07/1.25                           ( k1_zfmisc_1 @
% 1.07/1.25                             ( k2_zfmisc_1 @
% 1.07/1.25                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                       ( ![F:$i]:
% 1.07/1.25                         ( ( ( v1_funct_1 @ F ) & 
% 1.07/1.25                             ( v1_funct_2 @
% 1.07/1.25                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                             ( m1_subset_1 @
% 1.07/1.25                               F @ 
% 1.07/1.25                               ( k1_zfmisc_1 @
% 1.07/1.25                                 ( k2_zfmisc_1 @
% 1.07/1.25                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                           ( ![G:$i]:
% 1.07/1.25                             ( ( ( v1_funct_1 @ G ) & 
% 1.07/1.25                                 ( v1_funct_2 @
% 1.07/1.25                                   G @ ( u1_struct_0 @ D ) @ 
% 1.07/1.25                                   ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                                 ( m1_subset_1 @
% 1.07/1.25                                   G @ 
% 1.07/1.25                                   ( k1_zfmisc_1 @
% 1.07/1.25                                     ( k2_zfmisc_1 @
% 1.07/1.25                                       ( u1_struct_0 @ D ) @ 
% 1.07/1.25                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                               ( ( ( ( D ) = ( A ) ) & 
% 1.07/1.25                                   ( r1_funct_2 @
% 1.07/1.25                                     ( u1_struct_0 @ A ) @ 
% 1.07/1.25                                     ( u1_struct_0 @ B ) @ 
% 1.07/1.25                                     ( u1_struct_0 @ D ) @ 
% 1.07/1.25                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.07/1.25                                 ( ( r2_funct_2 @
% 1.07/1.25                                     ( u1_struct_0 @ C ) @ 
% 1.07/1.25                                     ( u1_struct_0 @ B ) @ 
% 1.07/1.25                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.07/1.25                                   ( r2_funct_2 @
% 1.07/1.25                                     ( u1_struct_0 @ C ) @ 
% 1.07/1.25                                     ( u1_struct_0 @ B ) @ 
% 1.07/1.25                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.25    (~( ![A:$i]:
% 1.07/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.07/1.25            ( l1_pre_topc @ A ) ) =>
% 1.07/1.25          ( ![B:$i]:
% 1.07/1.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.07/1.25                ( l1_pre_topc @ B ) ) =>
% 1.07/1.25              ( ![C:$i]:
% 1.07/1.25                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.07/1.25                  ( ![D:$i]:
% 1.07/1.25                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.07/1.25                      ( ![E:$i]:
% 1.07/1.25                        ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.25                            ( v1_funct_2 @
% 1.07/1.25                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                            ( m1_subset_1 @
% 1.07/1.25                              E @ 
% 1.07/1.25                              ( k1_zfmisc_1 @
% 1.07/1.25                                ( k2_zfmisc_1 @
% 1.07/1.25                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                          ( ![F:$i]:
% 1.07/1.25                            ( ( ( v1_funct_1 @ F ) & 
% 1.07/1.25                                ( v1_funct_2 @
% 1.07/1.25                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                                ( m1_subset_1 @
% 1.07/1.25                                  F @ 
% 1.07/1.25                                  ( k1_zfmisc_1 @
% 1.07/1.25                                    ( k2_zfmisc_1 @
% 1.07/1.25                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                              ( ![G:$i]:
% 1.07/1.25                                ( ( ( v1_funct_1 @ G ) & 
% 1.07/1.25                                    ( v1_funct_2 @
% 1.07/1.25                                      G @ ( u1_struct_0 @ D ) @ 
% 1.07/1.25                                      ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                                    ( m1_subset_1 @
% 1.07/1.25                                      G @ 
% 1.07/1.25                                      ( k1_zfmisc_1 @
% 1.07/1.25                                        ( k2_zfmisc_1 @
% 1.07/1.25                                          ( u1_struct_0 @ D ) @ 
% 1.07/1.25                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                                  ( ( ( ( D ) = ( A ) ) & 
% 1.07/1.25                                      ( r1_funct_2 @
% 1.07/1.25                                        ( u1_struct_0 @ A ) @ 
% 1.07/1.25                                        ( u1_struct_0 @ B ) @ 
% 1.07/1.25                                        ( u1_struct_0 @ D ) @ 
% 1.07/1.25                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.07/1.25                                    ( ( r2_funct_2 @
% 1.07/1.25                                        ( u1_struct_0 @ C ) @ 
% 1.07/1.25                                        ( u1_struct_0 @ B ) @ 
% 1.07/1.25                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.07/1.25                                      ( r2_funct_2 @
% 1.07/1.25                                        ( u1_struct_0 @ C ) @ 
% 1.07/1.25                                        ( u1_struct_0 @ B ) @ 
% 1.07/1.25                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.07/1.25    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.07/1.25  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('2', plain, (((sk_D) = (sk_A))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.07/1.25  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('5', plain, (((sk_D) = (sk_A))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.25  thf('7', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('8', plain, (((sk_D) = (sk_A))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('9', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(t78_tmap_1, axiom,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.25       ( ![B:$i]:
% 1.07/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.07/1.25             ( l1_pre_topc @ B ) ) =>
% 1.07/1.25           ( ![C:$i]:
% 1.07/1.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.07/1.25               ( ![D:$i]:
% 1.07/1.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.07/1.25                   ( ![E:$i]:
% 1.07/1.25                     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.25                         ( v1_funct_2 @
% 1.07/1.25                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                         ( m1_subset_1 @
% 1.07/1.25                           E @ 
% 1.07/1.25                           ( k1_zfmisc_1 @
% 1.07/1.25                             ( k2_zfmisc_1 @
% 1.07/1.25                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25                       ( ( m1_pre_topc @ C @ D ) =>
% 1.07/1.25                         ( r2_funct_2 @
% 1.07/1.25                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.07/1.25                           ( k3_tmap_1 @
% 1.07/1.25                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 1.07/1.25                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.25  thf('10', plain,
% 1.07/1.25      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.07/1.25         ((v2_struct_0 @ X39)
% 1.07/1.25          | ~ (v2_pre_topc @ X39)
% 1.07/1.25          | ~ (l1_pre_topc @ X39)
% 1.07/1.25          | (v2_struct_0 @ X40)
% 1.07/1.25          | ~ (m1_pre_topc @ X40 @ X41)
% 1.07/1.25          | ~ (m1_pre_topc @ X42 @ X40)
% 1.07/1.25          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X39) @ 
% 1.07/1.25             (k3_tmap_1 @ X41 @ X39 @ X40 @ X42 @ 
% 1.07/1.25              (k2_tmap_1 @ X41 @ X39 @ X43 @ X40)) @ 
% 1.07/1.25             (k2_tmap_1 @ X41 @ X39 @ X43 @ X42))
% 1.07/1.25          | ~ (m1_subset_1 @ X43 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 1.07/1.25          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 1.07/1.25          | ~ (v1_funct_1 @ X43)
% 1.07/1.25          | ~ (m1_pre_topc @ X42 @ X41)
% 1.07/1.25          | (v2_struct_0 @ X42)
% 1.07/1.25          | ~ (l1_pre_topc @ X41)
% 1.07/1.25          | ~ (v2_pre_topc @ X41)
% 1.07/1.25          | (v2_struct_0 @ X41))),
% 1.07/1.25      inference('cnf', [status(esa)], [t78_tmap_1])).
% 1.07/1.25  thf('11', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_D)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ X0)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 1.07/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)) @ 
% 1.07/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.25  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('13', plain, (((sk_D) = (sk_A))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('14', plain, ((v2_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.07/1.25  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('16', plain, (((sk_D) = (sk_A))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.25  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('19', plain,
% 1.07/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('20', plain, (((sk_D) = (sk_A))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('21', plain,
% 1.07/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.25  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('24', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ X0)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 1.07/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)) @ 
% 1.07/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)],
% 1.07/1.25                ['11', '14', '17', '18', '21', '22', '23'])).
% 1.07/1.25  thf('25', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ X0)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.07/1.25          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ 
% 1.07/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.07/1.25             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.07/1.25          | (v2_struct_0 @ sk_C)
% 1.07/1.25          | (v2_struct_0 @ sk_D))),
% 1.07/1.25      inference('sup-', [status(thm)], ['6', '24'])).
% 1.07/1.25  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.25  thf('27', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(d4_tmap_1, axiom,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.25       ( ![B:$i]:
% 1.07/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.07/1.25             ( l1_pre_topc @ B ) ) =>
% 1.07/1.25           ( ![C:$i]:
% 1.07/1.25             ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.25                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25                 ( m1_subset_1 @
% 1.07/1.25                   C @ 
% 1.07/1.25                   ( k1_zfmisc_1 @
% 1.07/1.25                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25               ( ![D:$i]:
% 1.07/1.25                 ( ( m1_pre_topc @ D @ A ) =>
% 1.07/1.25                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.07/1.25                     ( k2_partfun1 @
% 1.07/1.25                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.07/1.25                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.25  thf('28', plain,
% 1.07/1.25      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.25         ((v2_struct_0 @ X26)
% 1.07/1.25          | ~ (v2_pre_topc @ X26)
% 1.07/1.25          | ~ (l1_pre_topc @ X26)
% 1.07/1.25          | ~ (m1_pre_topc @ X27 @ X28)
% 1.07/1.25          | ((k2_tmap_1 @ X28 @ X26 @ X29 @ X27)
% 1.07/1.25              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26) @ 
% 1.07/1.25                 X29 @ (u1_struct_0 @ X27)))
% 1.07/1.25          | ~ (m1_subset_1 @ X29 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 1.07/1.25          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 1.07/1.25          | ~ (v1_funct_1 @ X29)
% 1.07/1.25          | ~ (l1_pre_topc @ X28)
% 1.07/1.25          | ~ (v2_pre_topc @ X28)
% 1.07/1.25          | (v2_struct_0 @ X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.07/1.25  thf('29', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_D)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.07/1.25              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25                 sk_E @ (u1_struct_0 @ X0)))
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['27', '28'])).
% 1.07/1.25  thf('30', plain, ((v2_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.07/1.25  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.25  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('33', plain,
% 1.07/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.25  thf('34', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(redefinition_k2_partfun1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25     ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.25       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.07/1.25  thf('35', plain,
% 1.07/1.25      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 1.07/1.25          | ~ (v1_funct_1 @ X8)
% 1.07/1.25          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 1.07/1.25      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.07/1.25  thf('36', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.07/1.25            X0) = (k7_relat_1 @ sk_E @ X0))
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E))),
% 1.07/1.25      inference('sup-', [status(thm)], ['34', '35'])).
% 1.07/1.25  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('38', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.07/1.25           X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.07/1.25      inference('demod', [status(thm)], ['36', '37'])).
% 1.07/1.25  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('41', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_D)
% 1.07/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.07/1.25              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)],
% 1.07/1.25                ['29', '30', '31', '32', '33', '38', '39', '40'])).
% 1.07/1.25  thf('42', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.25        | (v2_struct_0 @ sk_D))),
% 1.07/1.25      inference('sup-', [status(thm)], ['26', '41'])).
% 1.07/1.25  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('44', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_D)
% 1.07/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.07/1.25      inference('clc', [status(thm)], ['42', '43'])).
% 1.07/1.25  thf('45', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('46', plain,
% 1.07/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.25      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.25  thf('47', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ X0)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.07/1.25          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ 
% 1.07/1.25              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.07/1.25             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.25          | (v2_struct_0 @ sk_C)
% 1.07/1.25          | (v2_struct_0 @ sk_D))),
% 1.07/1.25      inference('demod', [status(thm)], ['25', '46'])).
% 1.07/1.25  thf('48', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_C)
% 1.07/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 1.07/1.25            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)) @ 
% 1.07/1.25           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.25        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['3', '47'])).
% 1.07/1.25  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.07/1.25  thf('50', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v2_struct_0 @ sk_D)
% 1.07/1.25          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.07/1.25              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)],
% 1.07/1.25                ['29', '30', '31', '32', '33', '38', '39', '40'])).
% 1.07/1.25  thf('51', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.07/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))
% 1.07/1.25        | (v2_struct_0 @ sk_D))),
% 1.07/1.25      inference('sup-', [status(thm)], ['49', '50'])).
% 1.07/1.25  thf('52', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(cc2_relset_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.25       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.25  thf('53', plain,
% 1.07/1.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.07/1.25         ((v4_relat_1 @ X5 @ X6)
% 1.07/1.25          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.07/1.25      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.25  thf('54', plain, ((v4_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 1.07/1.25      inference('sup-', [status(thm)], ['52', '53'])).
% 1.07/1.25  thf(t209_relat_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.07/1.25       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.07/1.25  thf('55', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (((X0) = (k7_relat_1 @ X0 @ X1))
% 1.07/1.25          | ~ (v4_relat_1 @ X0 @ X1)
% 1.07/1.25          | ~ (v1_relat_1 @ X0))),
% 1.07/1.25      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.07/1.25  thf('56', plain,
% 1.07/1.25      ((~ (v1_relat_1 @ sk_E)
% 1.07/1.25        | ((sk_E) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['54', '55'])).
% 1.07/1.25  thf('57', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(cc1_relset_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.25       ( v1_relat_1 @ C ) ))).
% 1.07/1.25  thf('58', plain,
% 1.07/1.25      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.07/1.25         ((v1_relat_1 @ X2)
% 1.07/1.25          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.07/1.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.25  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 1.07/1.25      inference('sup-', [status(thm)], ['57', '58'])).
% 1.07/1.25  thf('60', plain, (((sk_E) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))),
% 1.07/1.25      inference('demod', [status(thm)], ['56', '59'])).
% 1.07/1.25  thf('61', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))
% 1.07/1.25        | (v2_struct_0 @ sk_D))),
% 1.07/1.25      inference('demod', [status(thm)], ['51', '60'])).
% 1.07/1.25  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('63', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_D)
% 1.07/1.25        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E)))),
% 1.07/1.25      inference('clc', [status(thm)], ['61', '62'])).
% 1.07/1.25  thf('64', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('65', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.07/1.25      inference('clc', [status(thm)], ['63', '64'])).
% 1.07/1.25  thf('66', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.25  thf('67', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_C)
% 1.07/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.25        | (v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)], ['48', '65', '66'])).
% 1.07/1.25  thf('68', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.25        | (v2_struct_0 @ sk_C)
% 1.07/1.25        | (v2_struct_0 @ sk_D))),
% 1.07/1.25      inference('simplify', [status(thm)], ['67'])).
% 1.07/1.25  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.25  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.07/1.25  thf('71', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(dt_k3_tmap_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.07/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.07/1.25         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.07/1.25         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.07/1.25         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.07/1.25         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25         ( m1_subset_1 @
% 1.07/1.25           E @ 
% 1.07/1.25           ( k1_zfmisc_1 @
% 1.07/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.25       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.07/1.25         ( v1_funct_2 @
% 1.07/1.25           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.07/1.25           ( u1_struct_0 @ B ) ) & 
% 1.07/1.25         ( m1_subset_1 @
% 1.07/1.25           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.07/1.25           ( k1_zfmisc_1 @
% 1.07/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.07/1.25  thf('72', plain,
% 1.07/1.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X34 @ X35)
% 1.07/1.25          | ~ (m1_pre_topc @ X36 @ X35)
% 1.07/1.25          | ~ (l1_pre_topc @ X37)
% 1.07/1.25          | ~ (v2_pre_topc @ X37)
% 1.07/1.25          | (v2_struct_0 @ X37)
% 1.07/1.25          | ~ (l1_pre_topc @ X35)
% 1.07/1.25          | ~ (v2_pre_topc @ X35)
% 1.07/1.25          | (v2_struct_0 @ X35)
% 1.07/1.25          | ~ (v1_funct_1 @ X38)
% 1.07/1.25          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))
% 1.07/1.25          | ~ (m1_subset_1 @ X38 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))))
% 1.07/1.25          | (m1_subset_1 @ (k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38) @ 
% 1.07/1.25             (k1_zfmisc_1 @ 
% 1.07/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37)))))),
% 1.07/1.25      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.07/1.25  thf('73', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25           (k1_zfmisc_1 @ 
% 1.07/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (v2_pre_topc @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.07/1.25      inference('sup-', [status(thm)], ['71', '72'])).
% 1.07/1.25  thf('74', plain,
% 1.07/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.25  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('78', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25           (k1_zfmisc_1 @ 
% 1.07/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (v2_pre_topc @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.07/1.25      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.07/1.25  thf('79', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_D)
% 1.07/1.25          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25             (k1_zfmisc_1 @ 
% 1.07/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['70', '78'])).
% 1.07/1.25  thf('80', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.25  thf('81', plain, ((v2_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.07/1.25  thf('82', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ sk_D)
% 1.07/1.25          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25             (k1_zfmisc_1 @ 
% 1.07/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.07/1.25      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.07/1.25  thf('83', plain,
% 1.07/1.25      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25         (k1_zfmisc_1 @ 
% 1.07/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.25        | (v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['69', '82'])).
% 1.07/1.25  thf('84', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('85', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25           (k1_zfmisc_1 @ 
% 1.07/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.07/1.25      inference('clc', [status(thm)], ['83', '84'])).
% 1.07/1.25  thf('86', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('87', plain,
% 1.07/1.25      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('clc', [status(thm)], ['85', '86'])).
% 1.07/1.25  thf(redefinition_r2_funct_2, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.25         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.25       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.07/1.25  thf('88', plain,
% 1.07/1.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.25          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.25          | ~ (v1_funct_1 @ X12)
% 1.07/1.25          | ~ (v1_funct_1 @ X15)
% 1.07/1.25          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.07/1.25          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.25          | ((X12) = (X15))
% 1.07/1.25          | ~ (r2_funct_2 @ X13 @ X14 @ X12 @ X15))),
% 1.07/1.25      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.07/1.25  thf('89', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.07/1.25          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.07/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ~ (v1_funct_1 @ X0)
% 1.07/1.25          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.07/1.25          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['87', '88'])).
% 1.07/1.25  thf('90', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.25  thf('91', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.07/1.25  thf('92', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf('93', plain,
% 1.07/1.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X34 @ X35)
% 1.07/1.25          | ~ (m1_pre_topc @ X36 @ X35)
% 1.07/1.25          | ~ (l1_pre_topc @ X37)
% 1.07/1.25          | ~ (v2_pre_topc @ X37)
% 1.07/1.25          | (v2_struct_0 @ X37)
% 1.07/1.25          | ~ (l1_pre_topc @ X35)
% 1.07/1.25          | ~ (v2_pre_topc @ X35)
% 1.07/1.25          | (v2_struct_0 @ X35)
% 1.07/1.25          | ~ (v1_funct_1 @ X38)
% 1.07/1.25          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))
% 1.07/1.25          | ~ (m1_subset_1 @ X38 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))))
% 1.07/1.25          | (v1_funct_1 @ (k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38)))),
% 1.07/1.25      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.07/1.25  thf('94', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.07/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (v2_pre_topc @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.07/1.25      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.25  thf('95', plain,
% 1.07/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.25  thf('96', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('97', plain, ((v2_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('99', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (v2_pre_topc @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.07/1.25      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 1.07/1.25  thf('100', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_D)
% 1.07/1.25          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['91', '99'])).
% 1.07/1.25  thf('101', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.25  thf('102', plain, ((v2_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.07/1.25  thf('103', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ sk_D)
% 1.07/1.25          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.07/1.25      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.07/1.25  thf('104', plain,
% 1.07/1.25      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.07/1.25        | (v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['90', '103'])).
% 1.07/1.25  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('106', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)))),
% 1.07/1.25      inference('clc', [status(thm)], ['104', '105'])).
% 1.07/1.25  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('108', plain,
% 1.07/1.25      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 1.07/1.25      inference('clc', [status(thm)], ['106', '107'])).
% 1.07/1.25  thf('109', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.25  thf('110', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['1', '2'])).
% 1.07/1.25  thf('111', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf('112', plain,
% 1.07/1.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X34 @ X35)
% 1.07/1.25          | ~ (m1_pre_topc @ X36 @ X35)
% 1.07/1.25          | ~ (l1_pre_topc @ X37)
% 1.07/1.25          | ~ (v2_pre_topc @ X37)
% 1.07/1.25          | (v2_struct_0 @ X37)
% 1.07/1.25          | ~ (l1_pre_topc @ X35)
% 1.07/1.25          | ~ (v2_pre_topc @ X35)
% 1.07/1.25          | (v2_struct_0 @ X35)
% 1.07/1.25          | ~ (v1_funct_1 @ X38)
% 1.07/1.25          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))
% 1.07/1.25          | ~ (m1_subset_1 @ X38 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X37))))
% 1.07/1.25          | (v1_funct_2 @ (k3_tmap_1 @ X35 @ X37 @ X36 @ X34 @ X38) @ 
% 1.07/1.25             (u1_struct_0 @ X34) @ (u1_struct_0 @ X37)))),
% 1.07/1.25      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.07/1.25  thf('113', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (v2_pre_topc @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_B)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_B)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.07/1.25      inference('sup-', [status(thm)], ['111', '112'])).
% 1.07/1.25  thf('114', plain,
% 1.07/1.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.25  thf('115', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('116', plain, ((v2_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('118', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | (v2_struct_0 @ X1)
% 1.07/1.25          | ~ (v2_pre_topc @ X1)
% 1.07/1.25          | ~ (l1_pre_topc @ X1)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.07/1.25          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.07/1.25      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 1.07/1.25  thf('119', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_D)
% 1.07/1.25          | ~ (v2_pre_topc @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_D)
% 1.07/1.25          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['110', '118'])).
% 1.07/1.25  thf('120', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.25  thf('121', plain, ((v2_pre_topc @ sk_D)),
% 1.07/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.07/1.25  thf('122', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.07/1.25          | (v2_struct_0 @ sk_B)
% 1.07/1.25          | (v2_struct_0 @ sk_D)
% 1.07/1.25          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.07/1.25             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.25      inference('demod', [status(thm)], ['119', '120', '121'])).
% 1.07/1.25  thf('123', plain,
% 1.07/1.25      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.25        | (v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_B))),
% 1.07/1.25      inference('sup-', [status(thm)], ['109', '122'])).
% 1.07/1.25  thf('124', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('125', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_B)
% 1.07/1.25        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.25      inference('clc', [status(thm)], ['123', '124'])).
% 1.07/1.25  thf('126', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('127', plain,
% 1.07/1.25      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.25        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.25      inference('clc', [status(thm)], ['125', '126'])).
% 1.07/1.25  thf('128', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.25             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.07/1.25          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.07/1.25          | ~ (m1_subset_1 @ X0 @ 
% 1.07/1.25               (k1_zfmisc_1 @ 
% 1.07/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.25          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.25          | ~ (v1_funct_1 @ X0))),
% 1.07/1.25      inference('demod', [status(thm)], ['89', '108', '127'])).
% 1.07/1.25  thf('129', plain,
% 1.07/1.25      (((v2_struct_0 @ sk_D)
% 1.07/1.25        | (v2_struct_0 @ sk_C)
% 1.07/1.25        | (v2_struct_0 @ sk_B)
% 1.07/1.25        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.25        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.25             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.25        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.25             (k1_zfmisc_1 @ 
% 1.07/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.25        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.07/1.25            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['68', '128'])).
% 1.07/1.25  thf('130', plain,
% 1.07/1.25      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.25         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.25      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.25  thf('131', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_E @ 
% 1.07/1.25        (k1_zfmisc_1 @ 
% 1.07/1.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.25      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.25  thf(dt_k2_tmap_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.07/1.25         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.25         ( m1_subset_1 @
% 1.07/1.25           C @ 
% 1.07/1.25           ( k1_zfmisc_1 @
% 1.07/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.07/1.25         ( l1_struct_0 @ D ) ) =>
% 1.07/1.25       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.07/1.25         ( v1_funct_2 @
% 1.07/1.25           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.07/1.25           ( u1_struct_0 @ B ) ) & 
% 1.07/1.25         ( m1_subset_1 @
% 1.07/1.25           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.07/1.25           ( k1_zfmisc_1 @
% 1.07/1.25             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.07/1.25  thf('132', plain,
% 1.07/1.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X30 @ 
% 1.07/1.25             (k1_zfmisc_1 @ 
% 1.07/1.25              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 1.07/1.25          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 1.07/1.25          | ~ (v1_funct_1 @ X30)
% 1.07/1.25          | ~ (l1_struct_0 @ X32)
% 1.07/1.25          | ~ (l1_struct_0 @ X31)
% 1.07/1.25          | ~ (l1_struct_0 @ X33)
% 1.07/1.25          | (v1_funct_1 @ (k2_tmap_1 @ X31 @ X32 @ X30 @ X33)))),
% 1.07/1.25      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.07/1.25  thf('133', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.07/1.25          | ~ (l1_struct_0 @ X0)
% 1.07/1.25          | ~ (l1_struct_0 @ sk_D)
% 1.07/1.25          | ~ (l1_struct_0 @ sk_B)
% 1.07/1.25          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['131', '132'])).
% 1.07/1.26  thf('134', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.26      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.26  thf(dt_l1_pre_topc, axiom,
% 1.07/1.26    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.07/1.26  thf('135', plain,
% 1.07/1.26      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.07/1.26  thf('136', plain, ((l1_struct_0 @ sk_D)),
% 1.07/1.26      inference('sup-', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('138', plain,
% 1.07/1.26      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.07/1.26  thf('139', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.26      inference('sup-', [status(thm)], ['137', '138'])).
% 1.07/1.26  thf('140', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('141', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.26  thf('142', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.07/1.26          | ~ (l1_struct_0 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['133', '136', '139', '140', '141'])).
% 1.07/1.26  thf('143', plain,
% 1.07/1.26      (((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | ~ (l1_struct_0 @ sk_C))),
% 1.07/1.26      inference('sup+', [status(thm)], ['130', '142'])).
% 1.07/1.26  thf('144', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.07/1.26      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.26  thf(dt_m1_pre_topc, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( l1_pre_topc @ A ) =>
% 1.07/1.26       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.07/1.26  thf('145', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i]:
% 1.07/1.26         (~ (m1_pre_topc @ X17 @ X18)
% 1.07/1.26          | (l1_pre_topc @ X17)
% 1.07/1.26          | ~ (l1_pre_topc @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.07/1.26  thf('146', plain, ((~ (l1_pre_topc @ sk_D) | (l1_pre_topc @ sk_C))),
% 1.07/1.26      inference('sup-', [status(thm)], ['144', '145'])).
% 1.07/1.26  thf('147', plain, ((l1_pre_topc @ sk_D)),
% 1.07/1.26      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.26  thf('148', plain, ((l1_pre_topc @ sk_C)),
% 1.07/1.26      inference('demod', [status(thm)], ['146', '147'])).
% 1.07/1.26  thf('149', plain,
% 1.07/1.26      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.07/1.26  thf('150', plain, ((l1_struct_0 @ sk_C)),
% 1.07/1.26      inference('sup-', [status(thm)], ['148', '149'])).
% 1.07/1.26  thf('151', plain,
% 1.07/1.26      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('demod', [status(thm)], ['143', '150'])).
% 1.07/1.26  thf('152', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('153', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.26  thf('154', plain,
% 1.07/1.26      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X30 @ 
% 1.07/1.26             (k1_zfmisc_1 @ 
% 1.07/1.26              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 1.07/1.26          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 1.07/1.26          | ~ (v1_funct_1 @ X30)
% 1.07/1.26          | ~ (l1_struct_0 @ X32)
% 1.07/1.26          | ~ (l1_struct_0 @ X31)
% 1.07/1.26          | ~ (l1_struct_0 @ X33)
% 1.07/1.26          | (v1_funct_2 @ (k2_tmap_1 @ X31 @ X32 @ X30 @ X33) @ 
% 1.07/1.26             (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.07/1.26  thf('155', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | ~ (l1_struct_0 @ X0)
% 1.07/1.26          | ~ (l1_struct_0 @ sk_D)
% 1.07/1.26          | ~ (l1_struct_0 @ sk_B)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.26          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['153', '154'])).
% 1.07/1.26  thf('156', plain, ((l1_struct_0 @ sk_D)),
% 1.07/1.26      inference('sup-', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('157', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.26      inference('sup-', [status(thm)], ['137', '138'])).
% 1.07/1.26  thf('158', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('159', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.26  thf('160', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | ~ (l1_struct_0 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 1.07/1.26  thf('161', plain,
% 1.07/1.26      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ~ (l1_struct_0 @ sk_C))),
% 1.07/1.26      inference('sup+', [status(thm)], ['152', '160'])).
% 1.07/1.26  thf('162', plain, ((l1_struct_0 @ sk_C)),
% 1.07/1.26      inference('sup-', [status(thm)], ['148', '149'])).
% 1.07/1.26  thf('163', plain,
% 1.07/1.26      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['161', '162'])).
% 1.07/1.26  thf('164', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('165', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.26  thf('166', plain,
% 1.07/1.26      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X30 @ 
% 1.07/1.26             (k1_zfmisc_1 @ 
% 1.07/1.26              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 1.07/1.26          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 1.07/1.26          | ~ (v1_funct_1 @ X30)
% 1.07/1.26          | ~ (l1_struct_0 @ X32)
% 1.07/1.26          | ~ (l1_struct_0 @ X31)
% 1.07/1.26          | ~ (l1_struct_0 @ X33)
% 1.07/1.26          | (m1_subset_1 @ (k2_tmap_1 @ X31 @ X32 @ X30 @ X33) @ 
% 1.07/1.26             (k1_zfmisc_1 @ 
% 1.07/1.26              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.07/1.26  thf('167', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26           (k1_zfmisc_1 @ 
% 1.07/1.26            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (l1_struct_0 @ X0)
% 1.07/1.26          | ~ (l1_struct_0 @ sk_D)
% 1.07/1.26          | ~ (l1_struct_0 @ sk_B)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.26          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['165', '166'])).
% 1.07/1.26  thf('168', plain, ((l1_struct_0 @ sk_D)),
% 1.07/1.26      inference('sup-', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.26      inference('sup-', [status(thm)], ['137', '138'])).
% 1.07/1.26  thf('170', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('171', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.26  thf('172', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26           (k1_zfmisc_1 @ 
% 1.07/1.26            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (l1_struct_0 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 1.07/1.26  thf('173', plain,
% 1.07/1.26      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26         (k1_zfmisc_1 @ 
% 1.07/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26        | ~ (l1_struct_0 @ sk_C))),
% 1.07/1.26      inference('sup+', [status(thm)], ['164', '172'])).
% 1.07/1.26  thf('174', plain, ((l1_struct_0 @ sk_C)),
% 1.07/1.26      inference('sup-', [status(thm)], ['148', '149'])).
% 1.07/1.26  thf('175', plain,
% 1.07/1.26      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['173', '174'])).
% 1.07/1.26  thf('176', plain,
% 1.07/1.26      (((v2_struct_0 @ sk_D)
% 1.07/1.26        | (v2_struct_0 @ sk_C)
% 1.07/1.26        | (v2_struct_0 @ sk_B)
% 1.07/1.26        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.07/1.26            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.07/1.26      inference('demod', [status(thm)], ['129', '151', '163', '175'])).
% 1.07/1.26  thf('177', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.07/1.26        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('178', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.07/1.26      inference('split', [status(esa)], ['177'])).
% 1.07/1.26  thf('179', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('180', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['178', '179'])).
% 1.07/1.26  thf('181', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26           (k1_zfmisc_1 @ 
% 1.07/1.26            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (l1_struct_0 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 1.07/1.26  thf('182', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.26          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | ~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v1_funct_1 @ X15)
% 1.07/1.26          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.07/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.26          | ((X12) = (X15))
% 1.07/1.26          | ~ (r2_funct_2 @ X13 @ X14 @ X12 @ X15))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.07/1.26  thf('183', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (l1_struct_0 @ X0)
% 1.07/1.26          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 1.07/1.26          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) = (X1))
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | ~ (v1_funct_1 @ X1)
% 1.07/1.26          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.07/1.26          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['181', '182'])).
% 1.07/1.26  thf('184', plain,
% 1.07/1.26      (((~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.07/1.26            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.07/1.26         | ~ (v1_funct_1 @ sk_F)
% 1.07/1.26         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26         | ~ (m1_subset_1 @ sk_F @ 
% 1.07/1.26              (k1_zfmisc_1 @ 
% 1.07/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26         | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) = (sk_F))
% 1.07/1.26         | ~ (l1_struct_0 @ sk_C)))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['180', '183'])).
% 1.07/1.26  thf('185', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('186', plain,
% 1.07/1.26      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['161', '162'])).
% 1.07/1.26  thf('187', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('188', plain,
% 1.07/1.26      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('demod', [status(thm)], ['143', '150'])).
% 1.07/1.26  thf('189', plain, ((v1_funct_1 @ sk_F)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('190', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('191', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_F @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('192', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('193', plain, ((l1_struct_0 @ sk_C)),
% 1.07/1.26      inference('sup-', [status(thm)], ['148', '149'])).
% 1.07/1.26  thf('194', plain,
% 1.07/1.26      ((((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F)))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)],
% 1.07/1.26                ['184', '185', '186', '187', '188', '189', '190', '191', 
% 1.07/1.26                 '192', '193'])).
% 1.07/1.26  thf('195', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.07/1.26        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('196', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('197', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('198', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.07/1.26        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('demod', [status(thm)], ['195', '196', '197'])).
% 1.07/1.26  thf('199', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('split', [status(esa)], ['198'])).
% 1.07/1.26  thf('200', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('201', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('split', [status(esa)], ['200'])).
% 1.07/1.26  thf('202', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('203', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['201', '202'])).
% 1.07/1.26  thf('204', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('sup-', [status(thm)], ['199', '203'])).
% 1.07/1.26  thf('205', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('206', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('207', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('208', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('demod', [status(thm)], ['205', '206', '207'])).
% 1.07/1.26  thf('209', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.07/1.26       ~
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.07/1.26      inference('split', [status(esa)], ['208'])).
% 1.07/1.26  thf('210', plain,
% 1.07/1.26      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('211', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('212', plain,
% 1.07/1.26      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.07/1.26      inference('demod', [status(thm)], ['210', '211'])).
% 1.07/1.26  thf('213', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.26  thf(redefinition_r1_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.26     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.07/1.26         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.07/1.26         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.07/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.26       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.07/1.26  thf('214', plain,
% 1.07/1.26      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.07/1.26          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 1.07/1.26          | ~ (v1_funct_1 @ X20)
% 1.07/1.26          | (v1_xboole_0 @ X23)
% 1.07/1.26          | (v1_xboole_0 @ X22)
% 1.07/1.26          | ~ (v1_funct_1 @ X24)
% 1.07/1.26          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 1.07/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 1.07/1.26          | ((X20) = (X24))
% 1.07/1.26          | ~ (r1_funct_2 @ X21 @ X22 @ X25 @ X23 @ X20 @ X24))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.07/1.26  thf('215', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.07/1.26             X1 @ sk_E @ X0)
% 1.07/1.26          | ((sk_E) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | (v1_xboole_0 @ X1)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_E)
% 1.07/1.26          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['213', '214'])).
% 1.07/1.26  thf('216', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('217', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.26  thf('218', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.07/1.26             X1 @ sk_E @ X0)
% 1.07/1.26          | ((sk_E) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | (v1_xboole_0 @ X1))),
% 1.07/1.26      inference('demod', [status(thm)], ['215', '216', '217'])).
% 1.07/1.26  thf('219', plain,
% 1.07/1.26      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_1 @ sk_G)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ~ (m1_subset_1 @ sk_G @ 
% 1.07/1.26             (k1_zfmisc_1 @ 
% 1.07/1.26              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26        | ((sk_E) = (sk_G)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['212', '218'])).
% 1.07/1.26  thf('220', plain, ((v1_funct_1 @ sk_G)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('221', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('222', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_G @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('223', plain,
% 1.07/1.26      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ((sk_E) = (sk_G)))),
% 1.07/1.26      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 1.07/1.26  thf('224', plain,
% 1.07/1.26      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['223'])).
% 1.07/1.26  thf(fc2_struct_0, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.07/1.26       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.07/1.26  thf('225', plain,
% 1.07/1.26      (![X19 : $i]:
% 1.07/1.26         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 1.07/1.26          | ~ (l1_struct_0 @ X19)
% 1.07/1.26          | (v2_struct_0 @ X19))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.07/1.26  thf('226', plain,
% 1.07/1.26      ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['224', '225'])).
% 1.07/1.26  thf('227', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.26      inference('sup-', [status(thm)], ['137', '138'])).
% 1.07/1.26  thf('228', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['226', '227'])).
% 1.07/1.26  thf('229', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('230', plain, (((sk_E) = (sk_G))),
% 1.07/1.26      inference('clc', [status(thm)], ['228', '229'])).
% 1.07/1.26  thf('231', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('split', [status(esa)], ['177'])).
% 1.07/1.26  thf('232', plain, (((sk_D) = (sk_A))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('233', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['231', '232'])).
% 1.07/1.26  thf('234', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['230', '233'])).
% 1.07/1.26  thf('235', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.07/1.26          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['89', '108', '127'])).
% 1.07/1.26  thf('236', plain,
% 1.07/1.26      (((~ (v1_funct_1 @ sk_F)
% 1.07/1.26         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26         | ~ (m1_subset_1 @ sk_F @ 
% 1.07/1.26              (k1_zfmisc_1 @ 
% 1.07/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26         | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F))))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['234', '235'])).
% 1.07/1.26  thf('237', plain, ((v1_funct_1 @ sk_F)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('238', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('239', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_F @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('240', plain,
% 1.07/1.26      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 1.07/1.26  thf('241', plain,
% 1.07/1.26      (((v2_struct_0 @ sk_B)
% 1.07/1.26        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.07/1.26           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | (v2_struct_0 @ sk_C)
% 1.07/1.26        | (v2_struct_0 @ sk_D))),
% 1.07/1.26      inference('simplify', [status(thm)], ['67'])).
% 1.07/1.26  thf('242', plain,
% 1.07/1.26      ((((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26          (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26         | (v2_struct_0 @ sk_D)
% 1.07/1.26         | (v2_struct_0 @ sk_C)
% 1.07/1.26         | (v2_struct_0 @ sk_B)))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['240', '241'])).
% 1.07/1.26  thf('243', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.07/1.26           (k1_zfmisc_1 @ 
% 1.07/1.26            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (l1_struct_0 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 1.07/1.26  thf('244', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_F @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('245', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.26          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | ~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v1_funct_1 @ X15)
% 1.07/1.26          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.07/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.26          | ((X12) = (X15))
% 1.07/1.26          | ~ (r2_funct_2 @ X13 @ X14 @ X12 @ X15))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.07/1.26  thf('246', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             X0)
% 1.07/1.26          | ((sk_F) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_F)
% 1.07/1.26          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['244', '245'])).
% 1.07/1.26  thf('247', plain, ((v1_funct_1 @ sk_F)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('248', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('249', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             X0)
% 1.07/1.26          | ((sk_F) = (X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ 
% 1.07/1.26               (k1_zfmisc_1 @ 
% 1.07/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.07/1.26          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['246', '247', '248'])).
% 1.07/1.26  thf('250', plain,
% 1.07/1.26      ((~ (l1_struct_0 @ sk_C)
% 1.07/1.26        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.07/1.26             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ((sk_F) = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['243', '249'])).
% 1.07/1.26  thf('251', plain, ((l1_struct_0 @ sk_C)),
% 1.07/1.26      inference('sup-', [status(thm)], ['148', '149'])).
% 1.07/1.26  thf('252', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.07/1.26        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.07/1.26             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ((sk_F) = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 1.07/1.26      inference('demod', [status(thm)], ['250', '251'])).
% 1.07/1.26  thf('253', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('254', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('255', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('256', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('257', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.07/1.26      inference('demod', [status(thm)], ['252', '253', '254', '255', '256'])).
% 1.07/1.26  thf('258', plain,
% 1.07/1.26      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.07/1.26        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('demod', [status(thm)], ['161', '162'])).
% 1.07/1.26  thf('259', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.07/1.26      inference('demod', [status(thm)], ['257', '258'])).
% 1.07/1.26  thf('260', plain,
% 1.07/1.26      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('demod', [status(thm)], ['143', '150'])).
% 1.07/1.26  thf('261', plain,
% 1.07/1.26      ((((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.07/1.26        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.07/1.26      inference('demod', [status(thm)], ['259', '260'])).
% 1.07/1.26  thf('262', plain,
% 1.07/1.26      ((((v2_struct_0 @ sk_B)
% 1.07/1.26         | (v2_struct_0 @ sk_C)
% 1.07/1.26         | (v2_struct_0 @ sk_D)
% 1.07/1.26         | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['242', '261'])).
% 1.07/1.26  thf('263', plain,
% 1.07/1.26      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.07/1.26         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.07/1.26      inference('clc', [status(thm)], ['44', '45'])).
% 1.07/1.26  thf('264', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.07/1.26      inference('split', [status(esa)], ['208'])).
% 1.07/1.26  thf('265', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['263', '264'])).
% 1.07/1.26  thf('266', plain,
% 1.07/1.26      (((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26            sk_F)
% 1.07/1.26         | (v2_struct_0 @ sk_D)
% 1.07/1.26         | (v2_struct_0 @ sk_C)
% 1.07/1.26         | (v2_struct_0 @ sk_B)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['262', '265'])).
% 1.07/1.26  thf('267', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_F @ 
% 1.07/1.26        (k1_zfmisc_1 @ 
% 1.07/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('268', plain,
% 1.07/1.26      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.26          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 1.07/1.26          | ~ (v1_funct_1 @ X12)
% 1.07/1.26          | ~ (v1_funct_1 @ X15)
% 1.07/1.26          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.07/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.07/1.26          | (r2_funct_2 @ X13 @ X14 @ X12 @ X15)
% 1.07/1.26          | ((X12) != (X15)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.07/1.26  thf('269', plain,
% 1.07/1.26      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.26         ((r2_funct_2 @ X13 @ X14 @ X15 @ X15)
% 1.07/1.26          | ~ (v1_funct_1 @ X15)
% 1.07/1.26          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.07/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.07/1.26      inference('simplify', [status(thm)], ['268'])).
% 1.07/1.26  thf('270', plain,
% 1.07/1.26      ((~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.26        | ~ (v1_funct_1 @ sk_F)
% 1.07/1.26        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26           sk_F))),
% 1.07/1.26      inference('sup-', [status(thm)], ['267', '269'])).
% 1.07/1.26  thf('271', plain,
% 1.07/1.26      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('272', plain, ((v1_funct_1 @ sk_F)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('273', plain,
% 1.07/1.26      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.07/1.26      inference('demod', [status(thm)], ['270', '271', '272'])).
% 1.07/1.26  thf('274', plain,
% 1.07/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['266', '273'])).
% 1.07/1.26  thf('275', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('276', plain,
% 1.07/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('clc', [status(thm)], ['274', '275'])).
% 1.07/1.26  thf('277', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('278', plain,
% 1.07/1.26      (((v2_struct_0 @ sk_C))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('clc', [status(thm)], ['276', '277'])).
% 1.07/1.26  thf('279', plain, (~ (v2_struct_0 @ sk_C)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('280', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.07/1.26      inference('sup-', [status(thm)], ['278', '279'])).
% 1.07/1.26  thf('281', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['231', '232'])).
% 1.07/1.26  thf('282', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('split', [status(esa)], ['208'])).
% 1.07/1.26  thf('283', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('sup-', [status(thm)], ['281', '282'])).
% 1.07/1.26  thf('284', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('split', [status(esa)], ['177'])).
% 1.07/1.26  thf('285', plain,
% 1.07/1.26      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.07/1.26      inference('sat_resolution*', [status(thm)],
% 1.07/1.26                ['204', '209', '280', '283', '284'])).
% 1.07/1.26  thf('286', plain, (((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F))),
% 1.07/1.26      inference('simpl_trail', [status(thm)], ['194', '285'])).
% 1.07/1.26  thf('287', plain,
% 1.07/1.26      (((v2_struct_0 @ sk_D)
% 1.07/1.26        | (v2_struct_0 @ sk_C)
% 1.07/1.26        | (v2_struct_0 @ sk_B)
% 1.07/1.26        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['176', '286'])).
% 1.07/1.26  thf('288', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['201', '202'])).
% 1.07/1.26  thf('289', plain, (((sk_E) = (sk_G))),
% 1.07/1.26      inference('clc', [status(thm)], ['228', '229'])).
% 1.07/1.26  thf('290', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.07/1.26         <= (~
% 1.07/1.26             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.07/1.26      inference('demod', [status(thm)], ['288', '289'])).
% 1.07/1.26  thf('291', plain,
% 1.07/1.26      (~
% 1.07/1.26       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.07/1.26      inference('sat_resolution*', [status(thm)], ['204', '209', '280', '283'])).
% 1.07/1.26  thf('292', plain,
% 1.07/1.26      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.26          (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.07/1.26      inference('simpl_trail', [status(thm)], ['290', '291'])).
% 1.07/1.26  thf('293', plain,
% 1.07/1.26      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.07/1.26           sk_F)
% 1.07/1.26        | (v2_struct_0 @ sk_B)
% 1.07/1.26        | (v2_struct_0 @ sk_C)
% 1.07/1.26        | (v2_struct_0 @ sk_D))),
% 1.07/1.26      inference('sup-', [status(thm)], ['287', '292'])).
% 1.07/1.26  thf('294', plain,
% 1.07/1.26      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.07/1.26      inference('demod', [status(thm)], ['270', '271', '272'])).
% 1.07/1.26  thf('295', plain,
% 1.07/1.26      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 1.07/1.26      inference('demod', [status(thm)], ['293', '294'])).
% 1.07/1.26  thf('296', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('297', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.07/1.26      inference('clc', [status(thm)], ['295', '296'])).
% 1.07/1.26  thf('298', plain, (~ (v2_struct_0 @ sk_D)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('299', plain, ((v2_struct_0 @ sk_C)),
% 1.07/1.26      inference('clc', [status(thm)], ['297', '298'])).
% 1.07/1.26  thf('300', plain, ($false), inference('demod', [status(thm)], ['0', '299'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
