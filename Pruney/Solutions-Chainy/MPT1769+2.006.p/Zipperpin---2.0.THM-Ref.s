%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yja7a5HEy3

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:10 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  314 (3962 expanded)
%              Number of leaves         :   43 (1116 expanded)
%              Depth                    :   27
%              Number of atoms          : 3814 (220606 expanded)
%              Number of equality atoms :   68 (2527 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( m1_pre_topc @ X43 @ X41 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X40 ) @ ( k3_tmap_1 @ X42 @ X40 @ X41 @ X43 @ ( k2_tmap_1 @ X42 @ X40 @ X44 @ X41 ) ) @ ( k2_tmap_1 @ X42 @ X40 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X30 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k2_partfun1 @ X10 @ X11 @ X9 @ X12 )
        = ( k7_relat_1 @ X9 @ X12 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('72',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X36 @ X38 @ X37 @ X35 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('75',plain,(
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
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('77',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('83',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

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

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_funct_2 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('93',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('95',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X36 @ X38 @ X37 @ X35 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('96',plain,(
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
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('104',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('112',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('114',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X36 @ X38 @ X37 @ X35 @ X39 ) @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('115',plain,(
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
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('117',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('123',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','110','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['70','130'])).

thf('132',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('133',plain,(
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

thf('134',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X34 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X32 @ X33 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('137',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('138',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('141',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['135','138','141','142','143'])).

thf('145',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['132','144'])).

thf('146',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('147',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('148',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('150',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('152',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','152'])).

thf('154',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('155',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('156',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X34 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X32 @ X33 @ X31 @ X34 ) @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['136','137'])).

thf('159',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['139','140'])).

thf('160',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['154','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['150','151'])).

thf('165',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('167',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('168',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_struct_0 @ X33 )
      | ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['136','137'])).

thf('171',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['139','140'])).

thf('172',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['166','174'])).

thf('176',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['150','151'])).

thf('177',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['131','153','165','177'])).

thf('179',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
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

thf('183',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( X21 = X25 )
      | ~ ( r1_funct_2 @ X22 @ X23 @ X26 @ X24 @ X21 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('184',plain,(
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
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['181','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('194',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('195',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['139','140'])).

thf('197',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['197','198'])).

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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['199','203'])).

thf('205',plain,
    ( ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['178','204'])).

thf('206',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['200'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['131','153','165','177'])).

thf('208',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['197','198'])).

thf('209',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['209'])).

thf('211',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['208','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','110','129'])).

thf('215',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
        = sk_F )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['207','219'])).

thf('221',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('222',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['200'])).

thf('223',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['221','224'])).

thf('226',plain,
    ( ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['220','225'])).

thf('227',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_funct_2 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('229',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_funct_2 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['227','229'])).

thf('231',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['226','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['206','240'])).

thf('242',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['205','241'])).

thf('243',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['209'])).

thf('244',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('247',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_funct_2 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('248',plain,(
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
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
        = sk_F )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['245','248'])).

thf('250',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('251',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('252',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('253',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','152'])).

thf('254',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('258',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['150','151'])).

thf('259',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['249','250','251','252','253','254','255','256','257','258'])).

thf('260',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['209'])).

thf('261',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['206','240','260'])).

thf('262',plain,
    ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    = sk_F ),
    inference(simpl_trail,[status(thm)],['259','261'])).

thf('263',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['242','262','263'])).

thf('265',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['264','265'])).

thf('267',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['266','267'])).

thf('269',plain,(
    $false ),
    inference(demod,[status(thm)],['0','268'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yja7a5HEy3
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.38  % Solved by: fo/fo7.sh
% 1.19/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.38  % done 1808 iterations in 0.927s
% 1.19/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.38  % SZS output start Refutation
% 1.19/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.38  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.19/1.38  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.19/1.38  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.19/1.38  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.19/1.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.38  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.19/1.38  thf(sk_E_type, type, sk_E: $i).
% 1.19/1.38  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.19/1.38  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.19/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.38  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.19/1.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.19/1.38  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.19/1.38  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.19/1.38  thf(sk_G_type, type, sk_G: $i).
% 1.19/1.38  thf(sk_C_type, type, sk_C: $i).
% 1.19/1.38  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.19/1.38  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.38  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.19/1.38  thf(sk_F_type, type, sk_F: $i).
% 1.19/1.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.19/1.38  thf(sk_D_type, type, sk_D: $i).
% 1.19/1.38  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.19/1.38  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.38  thf(t80_tmap_1, conjecture,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.38             ( l1_pre_topc @ B ) ) =>
% 1.19/1.38           ( ![C:$i]:
% 1.19/1.38             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.38               ( ![D:$i]:
% 1.19/1.38                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.19/1.38                   ( ![E:$i]:
% 1.19/1.38                     ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.38                         ( v1_funct_2 @
% 1.19/1.38                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                         ( m1_subset_1 @
% 1.19/1.38                           E @ 
% 1.19/1.38                           ( k1_zfmisc_1 @
% 1.19/1.38                             ( k2_zfmisc_1 @
% 1.19/1.38                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                       ( ![F:$i]:
% 1.19/1.38                         ( ( ( v1_funct_1 @ F ) & 
% 1.19/1.38                             ( v1_funct_2 @
% 1.19/1.38                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                             ( m1_subset_1 @
% 1.19/1.38                               F @ 
% 1.19/1.38                               ( k1_zfmisc_1 @
% 1.19/1.38                                 ( k2_zfmisc_1 @
% 1.19/1.38                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                           ( ![G:$i]:
% 1.19/1.38                             ( ( ( v1_funct_1 @ G ) & 
% 1.19/1.38                                 ( v1_funct_2 @
% 1.19/1.38                                   G @ ( u1_struct_0 @ D ) @ 
% 1.19/1.38                                   ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                                 ( m1_subset_1 @
% 1.19/1.38                                   G @ 
% 1.19/1.38                                   ( k1_zfmisc_1 @
% 1.19/1.38                                     ( k2_zfmisc_1 @
% 1.19/1.38                                       ( u1_struct_0 @ D ) @ 
% 1.19/1.38                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                               ( ( ( ( D ) = ( A ) ) & 
% 1.19/1.38                                   ( r1_funct_2 @
% 1.19/1.38                                     ( u1_struct_0 @ A ) @ 
% 1.19/1.38                                     ( u1_struct_0 @ B ) @ 
% 1.19/1.38                                     ( u1_struct_0 @ D ) @ 
% 1.19/1.38                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.19/1.38                                 ( ( r2_funct_2 @
% 1.19/1.38                                     ( u1_struct_0 @ C ) @ 
% 1.19/1.38                                     ( u1_struct_0 @ B ) @ 
% 1.19/1.38                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.19/1.38                                   ( r2_funct_2 @
% 1.19/1.38                                     ( u1_struct_0 @ C ) @ 
% 1.19/1.38                                     ( u1_struct_0 @ B ) @ 
% 1.19/1.38                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.38    (~( ![A:$i]:
% 1.19/1.38        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.19/1.38            ( l1_pre_topc @ A ) ) =>
% 1.19/1.38          ( ![B:$i]:
% 1.19/1.38            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.38                ( l1_pre_topc @ B ) ) =>
% 1.19/1.38              ( ![C:$i]:
% 1.19/1.38                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.38                  ( ![D:$i]:
% 1.19/1.38                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.19/1.38                      ( ![E:$i]:
% 1.19/1.38                        ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.38                            ( v1_funct_2 @
% 1.19/1.38                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                            ( m1_subset_1 @
% 1.19/1.38                              E @ 
% 1.19/1.38                              ( k1_zfmisc_1 @
% 1.19/1.38                                ( k2_zfmisc_1 @
% 1.19/1.38                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                          ( ![F:$i]:
% 1.19/1.38                            ( ( ( v1_funct_1 @ F ) & 
% 1.19/1.38                                ( v1_funct_2 @
% 1.19/1.38                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                                ( m1_subset_1 @
% 1.19/1.38                                  F @ 
% 1.19/1.38                                  ( k1_zfmisc_1 @
% 1.19/1.38                                    ( k2_zfmisc_1 @
% 1.19/1.38                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                              ( ![G:$i]:
% 1.19/1.38                                ( ( ( v1_funct_1 @ G ) & 
% 1.19/1.38                                    ( v1_funct_2 @
% 1.19/1.38                                      G @ ( u1_struct_0 @ D ) @ 
% 1.19/1.38                                      ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                                    ( m1_subset_1 @
% 1.19/1.38                                      G @ 
% 1.19/1.38                                      ( k1_zfmisc_1 @
% 1.19/1.38                                        ( k2_zfmisc_1 @
% 1.19/1.38                                          ( u1_struct_0 @ D ) @ 
% 1.19/1.38                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                                  ( ( ( ( D ) = ( A ) ) & 
% 1.19/1.38                                      ( r1_funct_2 @
% 1.19/1.38                                        ( u1_struct_0 @ A ) @ 
% 1.19/1.38                                        ( u1_struct_0 @ B ) @ 
% 1.19/1.38                                        ( u1_struct_0 @ D ) @ 
% 1.19/1.38                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.19/1.38                                    ( ( r2_funct_2 @
% 1.19/1.38                                        ( u1_struct_0 @ C ) @ 
% 1.19/1.38                                        ( u1_struct_0 @ B ) @ 
% 1.19/1.38                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.19/1.38                                      ( r2_funct_2 @
% 1.19/1.38                                        ( u1_struct_0 @ C ) @ 
% 1.19/1.38                                        ( u1_struct_0 @ B ) @ 
% 1.19/1.38                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.19/1.38    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.19/1.38  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('2', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['1', '2'])).
% 1.19/1.38  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('5', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('7', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('8', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('9', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(t78_tmap_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.38             ( l1_pre_topc @ B ) ) =>
% 1.19/1.38           ( ![C:$i]:
% 1.19/1.38             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.38               ( ![D:$i]:
% 1.19/1.38                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.19/1.38                   ( ![E:$i]:
% 1.19/1.38                     ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.38                         ( v1_funct_2 @
% 1.19/1.38                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                         ( m1_subset_1 @
% 1.19/1.38                           E @ 
% 1.19/1.38                           ( k1_zfmisc_1 @
% 1.19/1.38                             ( k2_zfmisc_1 @
% 1.19/1.38                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38                       ( ( m1_pre_topc @ C @ D ) =>
% 1.19/1.38                         ( r2_funct_2 @
% 1.19/1.38                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.19/1.38                           ( k3_tmap_1 @
% 1.19/1.38                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 1.19/1.38                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.38  thf('10', plain,
% 1.19/1.38      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.19/1.38         ((v2_struct_0 @ X40)
% 1.19/1.38          | ~ (v2_pre_topc @ X40)
% 1.19/1.38          | ~ (l1_pre_topc @ X40)
% 1.19/1.38          | (v2_struct_0 @ X41)
% 1.19/1.38          | ~ (m1_pre_topc @ X41 @ X42)
% 1.19/1.38          | ~ (m1_pre_topc @ X43 @ X41)
% 1.19/1.38          | (r2_funct_2 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X40) @ 
% 1.19/1.38             (k3_tmap_1 @ X42 @ X40 @ X41 @ X43 @ 
% 1.19/1.38              (k2_tmap_1 @ X42 @ X40 @ X44 @ X41)) @ 
% 1.19/1.38             (k2_tmap_1 @ X42 @ X40 @ X44 @ X43))
% 1.19/1.38          | ~ (m1_subset_1 @ X44 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 1.19/1.38          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 1.19/1.38          | ~ (v1_funct_1 @ X44)
% 1.19/1.38          | ~ (m1_pre_topc @ X43 @ X42)
% 1.19/1.38          | (v2_struct_0 @ X43)
% 1.19/1.38          | ~ (l1_pre_topc @ X42)
% 1.19/1.38          | ~ (v2_pre_topc @ X42)
% 1.19/1.38          | (v2_struct_0 @ X42))),
% 1.19/1.38      inference('cnf', [status(esa)], [t78_tmap_1])).
% 1.19/1.38  thf('11', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_D)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_D)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ X0)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 1.19/1.38              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)) @ 
% 1.19/1.38             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_B)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['9', '10'])).
% 1.19/1.38  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('13', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('14', plain, ((v2_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.38  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('16', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('19', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('20', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('21', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('24', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ X0)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 1.19/1.38              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)) @ 
% 1.19/1.38             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)],
% 1.19/1.38                ['11', '14', '17', '18', '21', '22', '23'])).
% 1.19/1.38  thf('25', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ X0)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.19/1.38          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ 
% 1.19/1.38              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.19/1.38             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.19/1.38          | (v2_struct_0 @ sk_C)
% 1.19/1.38          | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('sup-', [status(thm)], ['6', '24'])).
% 1.19/1.38  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('27', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(d4_tmap_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.38             ( l1_pre_topc @ B ) ) =>
% 1.19/1.38           ( ![C:$i]:
% 1.19/1.38             ( ( ( v1_funct_1 @ C ) & 
% 1.19/1.38                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38                 ( m1_subset_1 @
% 1.19/1.38                   C @ 
% 1.19/1.38                   ( k1_zfmisc_1 @
% 1.19/1.38                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38               ( ![D:$i]:
% 1.19/1.38                 ( ( m1_pre_topc @ D @ A ) =>
% 1.19/1.38                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.19/1.38                     ( k2_partfun1 @
% 1.19/1.38                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.19/1.38                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.38  thf('28', plain,
% 1.19/1.38      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.19/1.38         ((v2_struct_0 @ X27)
% 1.19/1.38          | ~ (v2_pre_topc @ X27)
% 1.19/1.38          | ~ (l1_pre_topc @ X27)
% 1.19/1.38          | ~ (m1_pre_topc @ X28 @ X29)
% 1.19/1.38          | ((k2_tmap_1 @ X29 @ X27 @ X30 @ X28)
% 1.19/1.38              = (k2_partfun1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ 
% 1.19/1.38                 X30 @ (u1_struct_0 @ X28)))
% 1.19/1.38          | ~ (m1_subset_1 @ X30 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 1.19/1.38          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 1.19/1.38          | ~ (v1_funct_1 @ X30)
% 1.19/1.38          | ~ (l1_pre_topc @ X29)
% 1.19/1.38          | ~ (v2_pre_topc @ X29)
% 1.19/1.38          | (v2_struct_0 @ X29))),
% 1.19/1.38      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.19/1.38  thf('29', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_D)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_D)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_D)
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.19/1.38              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38                 sk_E @ (u1_struct_0 @ X0)))
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_B)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['27', '28'])).
% 1.19/1.38  thf('30', plain, ((v2_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.38  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('33', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('34', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(redefinition_k2_partfun1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.38     ( ( ( v1_funct_1 @ C ) & 
% 1.19/1.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.38       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.19/1.38  thf('35', plain,
% 1.19/1.38      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.19/1.38          | ~ (v1_funct_1 @ X9)
% 1.19/1.38          | ((k2_partfun1 @ X10 @ X11 @ X9 @ X12) = (k7_relat_1 @ X9 @ X12)))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.19/1.38  thf('36', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.19/1.38            X0) = (k7_relat_1 @ sk_E @ X0))
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E))),
% 1.19/1.38      inference('sup-', [status(thm)], ['34', '35'])).
% 1.19/1.38  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('38', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.19/1.38           X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['36', '37'])).
% 1.19/1.38  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('41', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_D)
% 1.19/1.38          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.19/1.38              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)],
% 1.19/1.38                ['29', '30', '31', '32', '33', '38', '39', '40'])).
% 1.19/1.38  thf('42', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38        | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('sup-', [status(thm)], ['26', '41'])).
% 1.19/1.38  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('44', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.19/1.38      inference('clc', [status(thm)], ['42', '43'])).
% 1.19/1.38  thf('45', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('46', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('47', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ X0)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.19/1.38          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ 
% 1.19/1.38              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.19/1.38             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38          | (v2_struct_0 @ sk_C)
% 1.19/1.38          | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('demod', [status(thm)], ['25', '46'])).
% 1.19/1.38  thf('48', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 1.19/1.38            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)) @ 
% 1.19/1.38           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['3', '47'])).
% 1.19/1.38  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['1', '2'])).
% 1.19/1.38  thf('50', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v2_struct_0 @ sk_D)
% 1.19/1.38          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.19/1.38              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)],
% 1.19/1.38                ['29', '30', '31', '32', '33', '38', '39', '40'])).
% 1.19/1.38  thf('51', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.19/1.38            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))
% 1.19/1.38        | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.38  thf('52', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(cc2_relset_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.38       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.19/1.38  thf('53', plain,
% 1.19/1.38      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.19/1.38         ((v4_relat_1 @ X6 @ X7)
% 1.19/1.38          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.19/1.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.38  thf('54', plain, ((v4_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 1.19/1.38      inference('sup-', [status(thm)], ['52', '53'])).
% 1.19/1.38  thf(t209_relat_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.19/1.38       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.19/1.38  thf('55', plain,
% 1.19/1.38      (![X4 : $i, X5 : $i]:
% 1.19/1.38         (((X4) = (k7_relat_1 @ X4 @ X5))
% 1.19/1.38          | ~ (v4_relat_1 @ X4 @ X5)
% 1.19/1.38          | ~ (v1_relat_1 @ X4))),
% 1.19/1.38      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.19/1.38  thf('56', plain,
% 1.19/1.38      ((~ (v1_relat_1 @ sk_E)
% 1.19/1.38        | ((sk_E) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['54', '55'])).
% 1.19/1.38  thf('57', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(cc2_relat_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.19/1.38  thf('58', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.19/1.38          | (v1_relat_1 @ X0)
% 1.19/1.38          | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.19/1.38  thf('59', plain,
% 1.19/1.38      ((~ (v1_relat_1 @ 
% 1.19/1.38           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.19/1.38        | (v1_relat_1 @ sk_E))),
% 1.19/1.38      inference('sup-', [status(thm)], ['57', '58'])).
% 1.19/1.38  thf(fc6_relat_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.19/1.38  thf('60', plain,
% 1.19/1.38      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.19/1.38  thf('61', plain, ((v1_relat_1 @ sk_E)),
% 1.19/1.38      inference('demod', [status(thm)], ['59', '60'])).
% 1.19/1.38  thf('62', plain, (((sk_E) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))),
% 1.19/1.38      inference('demod', [status(thm)], ['56', '61'])).
% 1.19/1.38  thf('63', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))
% 1.19/1.38        | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('demod', [status(thm)], ['51', '62'])).
% 1.19/1.38  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('65', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E)))),
% 1.19/1.38      inference('clc', [status(thm)], ['63', '64'])).
% 1.19/1.38  thf('66', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('67', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.19/1.38      inference('clc', [status(thm)], ['65', '66'])).
% 1.19/1.38  thf('68', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('69', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38        | (v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['48', '67', '68'])).
% 1.19/1.38  thf('70', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('simplify', [status(thm)], ['69'])).
% 1.19/1.38  thf('71', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('72', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['1', '2'])).
% 1.19/1.38  thf('73', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(dt_k3_tmap_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.19/1.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.19/1.38         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.19/1.38         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.19/1.38         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.19/1.38         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38         ( m1_subset_1 @
% 1.19/1.38           E @ 
% 1.19/1.38           ( k1_zfmisc_1 @
% 1.19/1.38             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.38       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.19/1.38         ( v1_funct_2 @
% 1.19/1.38           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.19/1.38           ( u1_struct_0 @ B ) ) & 
% 1.19/1.38         ( m1_subset_1 @
% 1.19/1.38           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.19/1.38           ( k1_zfmisc_1 @
% 1.19/1.38             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.19/1.38  thf('74', plain,
% 1.19/1.38      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X35 @ X36)
% 1.19/1.38          | ~ (m1_pre_topc @ X37 @ X36)
% 1.19/1.38          | ~ (l1_pre_topc @ X38)
% 1.19/1.38          | ~ (v2_pre_topc @ X38)
% 1.19/1.38          | (v2_struct_0 @ X38)
% 1.19/1.38          | ~ (l1_pre_topc @ X36)
% 1.19/1.38          | ~ (v2_pre_topc @ X36)
% 1.19/1.38          | (v2_struct_0 @ X36)
% 1.19/1.38          | ~ (v1_funct_1 @ X39)
% 1.19/1.38          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.19/1.38          | ~ (m1_subset_1 @ X39 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.19/1.38          | (m1_subset_1 @ (k3_tmap_1 @ X36 @ X38 @ X37 @ X35 @ X39) @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38)))))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.19/1.38  thf('75', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38           (k1_zfmisc_1 @ 
% 1.19/1.38            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (v2_pre_topc @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_B)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_B)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['73', '74'])).
% 1.19/1.38  thf('76', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('77', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('80', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38           (k1_zfmisc_1 @ 
% 1.19/1.38            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (v2_pre_topc @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.19/1.38      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 1.19/1.38  thf('81', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_D)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_D)
% 1.19/1.38          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['72', '80'])).
% 1.19/1.38  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf('83', plain, ((v2_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.38  thf('84', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ sk_D)
% 1.19/1.38          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.19/1.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.19/1.38  thf('85', plain,
% 1.19/1.38      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38         (k1_zfmisc_1 @ 
% 1.19/1.38          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38        | (v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['71', '84'])).
% 1.19/1.38  thf('86', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('87', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38           (k1_zfmisc_1 @ 
% 1.19/1.38            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.19/1.38      inference('clc', [status(thm)], ['85', '86'])).
% 1.19/1.38  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('89', plain,
% 1.19/1.38      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('clc', [status(thm)], ['87', '88'])).
% 1.19/1.38  thf(redefinition_r2_funct_2, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.38     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.19/1.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.19/1.38         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.19/1.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.38       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.19/1.38  thf('90', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.19/1.38          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 1.19/1.38          | ~ (v1_funct_1 @ X13)
% 1.19/1.38          | ~ (v1_funct_1 @ X16)
% 1.19/1.38          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 1.19/1.38          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.19/1.38          | ((X13) = (X16))
% 1.19/1.38          | ~ (r2_funct_2 @ X14 @ X15 @ X13 @ X16))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.19/1.38  thf('91', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.19/1.38          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.19/1.38          | ~ (m1_subset_1 @ X0 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ X0)
% 1.19/1.38          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.19/1.38          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['89', '90'])).
% 1.19/1.38  thf('92', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('93', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['1', '2'])).
% 1.19/1.38  thf('94', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf('95', plain,
% 1.19/1.38      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X35 @ X36)
% 1.19/1.38          | ~ (m1_pre_topc @ X37 @ X36)
% 1.19/1.38          | ~ (l1_pre_topc @ X38)
% 1.19/1.38          | ~ (v2_pre_topc @ X38)
% 1.19/1.38          | (v2_struct_0 @ X38)
% 1.19/1.38          | ~ (l1_pre_topc @ X36)
% 1.19/1.38          | ~ (v2_pre_topc @ X36)
% 1.19/1.38          | (v2_struct_0 @ X36)
% 1.19/1.38          | ~ (v1_funct_1 @ X39)
% 1.19/1.38          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.19/1.38          | ~ (m1_subset_1 @ X39 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.19/1.38          | (v1_funct_1 @ (k3_tmap_1 @ X36 @ X38 @ X37 @ X35 @ X39)))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.19/1.38  thf('96', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (v2_pre_topc @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_B)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_B)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['94', '95'])).
% 1.19/1.38  thf('97', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('101', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (v2_pre_topc @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.19/1.38      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 1.19/1.38  thf('102', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_D)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_D)
% 1.19/1.38          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['93', '101'])).
% 1.19/1.38  thf('103', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf('104', plain, ((v2_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.38  thf('105', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ sk_D)
% 1.19/1.38          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.19/1.38      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.19/1.38  thf('106', plain,
% 1.19/1.38      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.19/1.38        | (v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['92', '105'])).
% 1.19/1.38  thf('107', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('108', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)))),
% 1.19/1.38      inference('clc', [status(thm)], ['106', '107'])).
% 1.19/1.38  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('110', plain,
% 1.19/1.38      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 1.19/1.38      inference('clc', [status(thm)], ['108', '109'])).
% 1.19/1.38  thf('111', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('112', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['1', '2'])).
% 1.19/1.38  thf('113', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf('114', plain,
% 1.19/1.38      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X35 @ X36)
% 1.19/1.38          | ~ (m1_pre_topc @ X37 @ X36)
% 1.19/1.38          | ~ (l1_pre_topc @ X38)
% 1.19/1.38          | ~ (v2_pre_topc @ X38)
% 1.19/1.38          | (v2_struct_0 @ X38)
% 1.19/1.38          | ~ (l1_pre_topc @ X36)
% 1.19/1.38          | ~ (v2_pre_topc @ X36)
% 1.19/1.38          | (v2_struct_0 @ X36)
% 1.19/1.38          | ~ (v1_funct_1 @ X39)
% 1.19/1.38          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.19/1.38          | ~ (m1_subset_1 @ X39 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.19/1.38          | (v1_funct_2 @ (k3_tmap_1 @ X36 @ X38 @ X37 @ X35 @ X39) @ 
% 1.19/1.38             (u1_struct_0 @ X35) @ (u1_struct_0 @ X38)))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.19/1.38  thf('115', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (v2_pre_topc @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_B)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_B)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['113', '114'])).
% 1.19/1.38  thf('116', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('117', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('118', plain, ((v2_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('120', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | (v2_struct_0 @ X1)
% 1.19/1.38          | ~ (v2_pre_topc @ X1)
% 1.19/1.38          | ~ (l1_pre_topc @ X1)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.19/1.38          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.19/1.38      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 1.19/1.38  thf('121', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | ~ (l1_pre_topc @ sk_D)
% 1.19/1.38          | ~ (v2_pre_topc @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_D)
% 1.19/1.38          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['112', '120'])).
% 1.19/1.38  thf('122', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf('123', plain, ((v2_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.38  thf('124', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.38          | (v2_struct_0 @ sk_B)
% 1.19/1.38          | (v2_struct_0 @ sk_D)
% 1.19/1.38          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.19/1.38             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('demod', [status(thm)], ['121', '122', '123'])).
% 1.19/1.38  thf('125', plain,
% 1.19/1.38      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | (v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['111', '124'])).
% 1.19/1.38  thf('126', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('127', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B)
% 1.19/1.38        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('clc', [status(thm)], ['125', '126'])).
% 1.19/1.38  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('129', plain,
% 1.19/1.38      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.19/1.38        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('clc', [status(thm)], ['127', '128'])).
% 1.19/1.38  thf('130', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.19/1.38          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.19/1.38          | ~ (m1_subset_1 @ X0 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['91', '110', '129'])).
% 1.19/1.38  thf('131', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (v2_struct_0 @ sk_B)
% 1.19/1.38        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.19/1.38            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.19/1.38      inference('sup-', [status(thm)], ['70', '130'])).
% 1.19/1.38  thf('132', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('133', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(dt_k2_tmap_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.38     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.19/1.38         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.38         ( m1_subset_1 @
% 1.19/1.38           C @ 
% 1.19/1.38           ( k1_zfmisc_1 @
% 1.19/1.38             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.19/1.38         ( l1_struct_0 @ D ) ) =>
% 1.19/1.38       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.19/1.38         ( v1_funct_2 @
% 1.19/1.38           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.19/1.38           ( u1_struct_0 @ B ) ) & 
% 1.19/1.38         ( m1_subset_1 @
% 1.19/1.38           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.19/1.38           ( k1_zfmisc_1 @
% 1.19/1.38             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.19/1.38  thf('134', plain,
% 1.19/1.38      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X31 @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))))
% 1.19/1.38          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 1.19/1.38          | ~ (v1_funct_1 @ X31)
% 1.19/1.38          | ~ (l1_struct_0 @ X33)
% 1.19/1.38          | ~ (l1_struct_0 @ X32)
% 1.19/1.38          | ~ (l1_struct_0 @ X34)
% 1.19/1.38          | (v1_funct_1 @ (k2_tmap_1 @ X32 @ X33 @ X31 @ X34)))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.19/1.38  thf('135', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.19/1.38          | ~ (l1_struct_0 @ X0)
% 1.19/1.38          | ~ (l1_struct_0 @ sk_D)
% 1.19/1.38          | ~ (l1_struct_0 @ sk_B)
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['133', '134'])).
% 1.19/1.38  thf('136', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf(dt_l1_pre_topc, axiom,
% 1.19/1.38    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.19/1.38  thf('137', plain,
% 1.19/1.38      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.19/1.38  thf('138', plain, ((l1_struct_0 @ sk_D)),
% 1.19/1.38      inference('sup-', [status(thm)], ['136', '137'])).
% 1.19/1.38  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('140', plain,
% 1.19/1.38      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.19/1.38  thf('141', plain, ((l1_struct_0 @ sk_B)),
% 1.19/1.38      inference('sup-', [status(thm)], ['139', '140'])).
% 1.19/1.38  thf('142', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('143', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('144', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.19/1.38          | ~ (l1_struct_0 @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['135', '138', '141', '142', '143'])).
% 1.19/1.38  thf('145', plain,
% 1.19/1.38      (((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.19/1.38        | ~ (l1_struct_0 @ sk_C))),
% 1.19/1.38      inference('sup+', [status(thm)], ['132', '144'])).
% 1.19/1.38  thf('146', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf(dt_m1_pre_topc, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( l1_pre_topc @ A ) =>
% 1.19/1.38       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.19/1.38  thf('147', plain,
% 1.19/1.38      (![X18 : $i, X19 : $i]:
% 1.19/1.38         (~ (m1_pre_topc @ X18 @ X19)
% 1.19/1.38          | (l1_pre_topc @ X18)
% 1.19/1.38          | ~ (l1_pre_topc @ X19))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.19/1.38  thf('148', plain, ((~ (l1_pre_topc @ sk_D) | (l1_pre_topc @ sk_C))),
% 1.19/1.38      inference('sup-', [status(thm)], ['146', '147'])).
% 1.19/1.38  thf('149', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.38      inference('demod', [status(thm)], ['15', '16'])).
% 1.19/1.38  thf('150', plain, ((l1_pre_topc @ sk_C)),
% 1.19/1.38      inference('demod', [status(thm)], ['148', '149'])).
% 1.19/1.38  thf('151', plain,
% 1.19/1.38      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.19/1.38  thf('152', plain, ((l1_struct_0 @ sk_C)),
% 1.19/1.38      inference('sup-', [status(thm)], ['150', '151'])).
% 1.19/1.38  thf('153', plain,
% 1.19/1.38      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('demod', [status(thm)], ['145', '152'])).
% 1.19/1.38  thf('154', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('155', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf('156', plain,
% 1.19/1.38      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X31 @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))))
% 1.19/1.38          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 1.19/1.38          | ~ (v1_funct_1 @ X31)
% 1.19/1.38          | ~ (l1_struct_0 @ X33)
% 1.19/1.38          | ~ (l1_struct_0 @ X32)
% 1.19/1.38          | ~ (l1_struct_0 @ X34)
% 1.19/1.38          | (v1_funct_2 @ (k2_tmap_1 @ X32 @ X33 @ X31 @ X34) @ 
% 1.19/1.38             (u1_struct_0 @ X34) @ (u1_struct_0 @ X33)))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.19/1.38  thf('157', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.19/1.38           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (l1_struct_0 @ X0)
% 1.19/1.38          | ~ (l1_struct_0 @ sk_D)
% 1.19/1.38          | ~ (l1_struct_0 @ sk_B)
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['155', '156'])).
% 1.19/1.38  thf('158', plain, ((l1_struct_0 @ sk_D)),
% 1.19/1.38      inference('sup-', [status(thm)], ['136', '137'])).
% 1.19/1.38  thf('159', plain, ((l1_struct_0 @ sk_B)),
% 1.19/1.38      inference('sup-', [status(thm)], ['139', '140'])).
% 1.19/1.38  thf('160', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('161', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('162', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.19/1.38           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (l1_struct_0 @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 1.19/1.38  thf('163', plain,
% 1.19/1.38      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | ~ (l1_struct_0 @ sk_C))),
% 1.19/1.38      inference('sup+', [status(thm)], ['154', '162'])).
% 1.19/1.38  thf('164', plain, ((l1_struct_0 @ sk_C)),
% 1.19/1.38      inference('sup-', [status(thm)], ['150', '151'])).
% 1.19/1.38  thf('165', plain,
% 1.19/1.38      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['163', '164'])).
% 1.19/1.38  thf('166', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('167', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf('168', plain,
% 1.19/1.38      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X31 @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))))
% 1.19/1.38          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 1.19/1.38          | ~ (v1_funct_1 @ X31)
% 1.19/1.38          | ~ (l1_struct_0 @ X33)
% 1.19/1.38          | ~ (l1_struct_0 @ X32)
% 1.19/1.38          | ~ (l1_struct_0 @ X34)
% 1.19/1.38          | (m1_subset_1 @ (k2_tmap_1 @ X32 @ X33 @ X31 @ X34) @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33)))))),
% 1.19/1.38      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.19/1.38  thf('169', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.19/1.38           (k1_zfmisc_1 @ 
% 1.19/1.38            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (l1_struct_0 @ X0)
% 1.19/1.38          | ~ (l1_struct_0 @ sk_D)
% 1.19/1.38          | ~ (l1_struct_0 @ sk_B)
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['167', '168'])).
% 1.19/1.38  thf('170', plain, ((l1_struct_0 @ sk_D)),
% 1.19/1.38      inference('sup-', [status(thm)], ['136', '137'])).
% 1.19/1.38  thf('171', plain, ((l1_struct_0 @ sk_B)),
% 1.19/1.38      inference('sup-', [status(thm)], ['139', '140'])).
% 1.19/1.38  thf('172', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('173', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('174', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.19/1.38           (k1_zfmisc_1 @ 
% 1.19/1.38            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (l1_struct_0 @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 1.19/1.38  thf('175', plain,
% 1.19/1.38      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38         (k1_zfmisc_1 @ 
% 1.19/1.38          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38        | ~ (l1_struct_0 @ sk_C))),
% 1.19/1.38      inference('sup+', [status(thm)], ['166', '174'])).
% 1.19/1.38  thf('176', plain, ((l1_struct_0 @ sk_C)),
% 1.19/1.38      inference('sup-', [status(thm)], ['150', '151'])).
% 1.19/1.38  thf('177', plain,
% 1.19/1.38      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['175', '176'])).
% 1.19/1.38  thf('178', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (v2_struct_0 @ sk_B)
% 1.19/1.38        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.19/1.38            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.19/1.38      inference('demod', [status(thm)], ['131', '153', '165', '177'])).
% 1.19/1.38  thf('179', plain,
% 1.19/1.38      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('180', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('181', plain,
% 1.19/1.38      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.19/1.38      inference('demod', [status(thm)], ['179', '180'])).
% 1.19/1.38  thf('182', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_E @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('demod', [status(thm)], ['7', '8'])).
% 1.19/1.38  thf(redefinition_r1_funct_2, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.19/1.38     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.19/1.38         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.19/1.38         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.19/1.38         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.19/1.38         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.19/1.38       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.19/1.38  thf('183', plain,
% 1.19/1.38      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.19/1.38          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 1.19/1.38          | ~ (v1_funct_1 @ X21)
% 1.19/1.38          | (v1_xboole_0 @ X24)
% 1.19/1.38          | (v1_xboole_0 @ X23)
% 1.19/1.38          | ~ (v1_funct_1 @ X25)
% 1.19/1.38          | ~ (v1_funct_2 @ X25 @ X26 @ X24)
% 1.19/1.38          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 1.19/1.38          | ((X21) = (X25))
% 1.19/1.38          | ~ (r1_funct_2 @ X22 @ X23 @ X26 @ X24 @ X21 @ X25))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.19/1.38  thf('184', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.19/1.38             X1 @ sk_E @ X0)
% 1.19/1.38          | ((sk_E) = (X0))
% 1.19/1.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.19/1.38          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.19/1.38          | ~ (v1_funct_1 @ X0)
% 1.19/1.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | (v1_xboole_0 @ X1)
% 1.19/1.38          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.38          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['182', '183'])).
% 1.19/1.38  thf('185', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('186', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.19/1.38  thf('187', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.19/1.38             X1 @ sk_E @ X0)
% 1.19/1.38          | ((sk_E) = (X0))
% 1.19/1.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.19/1.38          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.19/1.38          | ~ (v1_funct_1 @ X0)
% 1.19/1.38          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | (v1_xboole_0 @ X1))),
% 1.19/1.38      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.19/1.38  thf('188', plain,
% 1.19/1.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | ~ (v1_funct_1 @ sk_G)
% 1.19/1.38        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | ~ (m1_subset_1 @ sk_G @ 
% 1.19/1.38             (k1_zfmisc_1 @ 
% 1.19/1.38              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38        | ((sk_E) = (sk_G)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['181', '187'])).
% 1.19/1.38  thf('189', plain, ((v1_funct_1 @ sk_G)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('190', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('191', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_G @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('192', plain,
% 1.19/1.38      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | ((sk_E) = (sk_G)))),
% 1.19/1.38      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 1.19/1.38  thf('193', plain,
% 1.19/1.38      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('simplify', [status(thm)], ['192'])).
% 1.19/1.38  thf(fc2_struct_0, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.19/1.38       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.19/1.38  thf('194', plain,
% 1.19/1.38      (![X20 : $i]:
% 1.19/1.38         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 1.19/1.38          | ~ (l1_struct_0 @ X20)
% 1.19/1.38          | (v2_struct_0 @ X20))),
% 1.19/1.38      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.19/1.38  thf('195', plain,
% 1.19/1.38      ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['193', '194'])).
% 1.19/1.38  thf('196', plain, ((l1_struct_0 @ sk_B)),
% 1.19/1.38      inference('sup-', [status(thm)], ['139', '140'])).
% 1.19/1.38  thf('197', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['195', '196'])).
% 1.19/1.38  thf('198', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('199', plain, (((sk_E) = (sk_G))),
% 1.19/1.38      inference('clc', [status(thm)], ['197', '198'])).
% 1.19/1.38  thf('200', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.19/1.38        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('201', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('split', [status(esa)], ['200'])).
% 1.19/1.38  thf('202', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('203', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)], ['201', '202'])).
% 1.19/1.38  thf('204', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['199', '203'])).
% 1.19/1.38  thf('205', plain,
% 1.19/1.38      (((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38            (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F)
% 1.19/1.38         | (v2_struct_0 @ sk_B)
% 1.19/1.38         | (v2_struct_0 @ sk_C)
% 1.19/1.38         | (v2_struct_0 @ sk_D)))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['178', '204'])).
% 1.19/1.38  thf('206', plain,
% 1.19/1.38      (~
% 1.19/1.38       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.19/1.38       ~
% 1.19/1.38       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.19/1.38      inference('split', [status(esa)], ['200'])).
% 1.19/1.38  thf('207', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_D)
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (v2_struct_0 @ sk_B)
% 1.19/1.38        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.19/1.38            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.19/1.38      inference('demod', [status(thm)], ['131', '153', '165', '177'])).
% 1.19/1.38  thf('208', plain, (((sk_E) = (sk_G))),
% 1.19/1.38      inference('clc', [status(thm)], ['197', '198'])).
% 1.19/1.38  thf('209', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.19/1.38        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('210', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('split', [status(esa)], ['209'])).
% 1.19/1.38  thf('211', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('212', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)], ['210', '211'])).
% 1.19/1.38  thf('213', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('sup+', [status(thm)], ['208', '212'])).
% 1.19/1.38  thf('214', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.19/1.38          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.19/1.38          | ~ (m1_subset_1 @ X0 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['91', '110', '129'])).
% 1.19/1.38  thf('215', plain,
% 1.19/1.38      (((~ (v1_funct_1 @ sk_F)
% 1.19/1.38         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38         | ~ (m1_subset_1 @ sk_F @ 
% 1.19/1.38              (k1_zfmisc_1 @ 
% 1.19/1.38               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38         | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F))))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['213', '214'])).
% 1.19/1.38  thf('216', plain, ((v1_funct_1 @ sk_F)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('217', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('218', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_F @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('219', plain,
% 1.19/1.38      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 1.19/1.38  thf('220', plain,
% 1.19/1.38      (((((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F))
% 1.19/1.38         | (v2_struct_0 @ sk_B)
% 1.19/1.38         | (v2_struct_0 @ sk_C)
% 1.19/1.38         | (v2_struct_0 @ sk_D)))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('sup+', [status(thm)], ['207', '219'])).
% 1.19/1.38  thf('221', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('222', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('split', [status(esa)], ['200'])).
% 1.19/1.38  thf('223', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('224', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)], ['222', '223'])).
% 1.19/1.38  thf('225', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['221', '224'])).
% 1.19/1.38  thf('226', plain,
% 1.19/1.38      (((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.19/1.38            sk_F)
% 1.19/1.38         | (v2_struct_0 @ sk_D)
% 1.19/1.38         | (v2_struct_0 @ sk_C)
% 1.19/1.38         | (v2_struct_0 @ sk_B)))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['220', '225'])).
% 1.19/1.38  thf('227', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_F @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('228', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.19/1.38          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 1.19/1.38          | ~ (v1_funct_1 @ X13)
% 1.19/1.38          | ~ (v1_funct_1 @ X16)
% 1.19/1.38          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 1.19/1.38          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.19/1.38          | (r2_funct_2 @ X14 @ X15 @ X13 @ X16)
% 1.19/1.38          | ((X13) != (X16)))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.19/1.38  thf('229', plain,
% 1.19/1.38      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.38         ((r2_funct_2 @ X14 @ X15 @ X16 @ X16)
% 1.19/1.38          | ~ (v1_funct_1 @ X16)
% 1.19/1.38          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 1.19/1.38          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.19/1.38      inference('simplify', [status(thm)], ['228'])).
% 1.19/1.38  thf('230', plain,
% 1.19/1.38      ((~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38        | ~ (v1_funct_1 @ sk_F)
% 1.19/1.38        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.19/1.38           sk_F))),
% 1.19/1.38      inference('sup-', [status(thm)], ['227', '229'])).
% 1.19/1.38  thf('231', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('232', plain, ((v1_funct_1 @ sk_F)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('233', plain,
% 1.19/1.38      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.19/1.38      inference('demod', [status(thm)], ['230', '231', '232'])).
% 1.19/1.38  thf('234', plain,
% 1.19/1.38      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)], ['226', '233'])).
% 1.19/1.38  thf('235', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('236', plain,
% 1.19/1.38      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('clc', [status(thm)], ['234', '235'])).
% 1.19/1.38  thf('237', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('238', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_C))
% 1.19/1.38         <= (~
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.19/1.38             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.19/1.38      inference('clc', [status(thm)], ['236', '237'])).
% 1.19/1.38  thf('239', plain, (~ (v2_struct_0 @ sk_C)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('240', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 1.19/1.38       ~
% 1.19/1.38       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.19/1.38      inference('sup-', [status(thm)], ['238', '239'])).
% 1.19/1.38  thf('241', plain,
% 1.19/1.38      (~
% 1.19/1.38       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.19/1.38      inference('sat_resolution*', [status(thm)], ['206', '240'])).
% 1.19/1.38  thf('242', plain,
% 1.19/1.38      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F)
% 1.19/1.38        | (v2_struct_0 @ sk_B)
% 1.19/1.38        | (v2_struct_0 @ sk_C)
% 1.19/1.38        | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('simpl_trail', [status(thm)], ['205', '241'])).
% 1.19/1.38  thf('243', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('split', [status(esa)], ['209'])).
% 1.19/1.38  thf('244', plain, (((sk_D) = (sk_A))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('245', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)], ['243', '244'])).
% 1.19/1.38  thf('246', plain,
% 1.19/1.38      (![X0 : $i]:
% 1.19/1.38         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.19/1.38           (k1_zfmisc_1 @ 
% 1.19/1.38            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (l1_struct_0 @ X0))),
% 1.19/1.38      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 1.19/1.38  thf('247', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.19/1.38          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 1.19/1.38          | ~ (v1_funct_1 @ X13)
% 1.19/1.38          | ~ (v1_funct_1 @ X16)
% 1.19/1.38          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 1.19/1.38          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.19/1.38          | ((X13) = (X16))
% 1.19/1.38          | ~ (r2_funct_2 @ X14 @ X15 @ X13 @ X16))),
% 1.19/1.38      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.19/1.38  thf('248', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (l1_struct_0 @ X0)
% 1.19/1.38          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 1.19/1.38          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) = (X1))
% 1.19/1.38          | ~ (m1_subset_1 @ X1 @ 
% 1.19/1.38               (k1_zfmisc_1 @ 
% 1.19/1.38                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.19/1.38          | ~ (v1_funct_1 @ X1)
% 1.19/1.38          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.19/1.38          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.19/1.38               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['246', '247'])).
% 1.19/1.38  thf('249', plain,
% 1.19/1.38      (((~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.19/1.38            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.19/1.38         | ~ (v1_funct_1 @ sk_F)
% 1.19/1.38         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.19/1.38         | ~ (m1_subset_1 @ sk_F @ 
% 1.19/1.38              (k1_zfmisc_1 @ 
% 1.19/1.38               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.19/1.38         | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) = (sk_F))
% 1.19/1.38         | ~ (l1_struct_0 @ sk_C)))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['245', '248'])).
% 1.19/1.38  thf('250', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('251', plain,
% 1.19/1.38      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.19/1.38        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('demod', [status(thm)], ['163', '164'])).
% 1.19/1.38  thf('252', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('253', plain,
% 1.19/1.38      ((v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('demod', [status(thm)], ['145', '152'])).
% 1.19/1.38  thf('254', plain, ((v1_funct_1 @ sk_F)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('255', plain,
% 1.19/1.38      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('256', plain,
% 1.19/1.38      ((m1_subset_1 @ sk_F @ 
% 1.19/1.38        (k1_zfmisc_1 @ 
% 1.19/1.38         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('257', plain,
% 1.19/1.38      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.19/1.38         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.19/1.38      inference('clc', [status(thm)], ['44', '45'])).
% 1.19/1.38  thf('258', plain, ((l1_struct_0 @ sk_C)),
% 1.19/1.38      inference('sup-', [status(thm)], ['150', '151'])).
% 1.19/1.38  thf('259', plain,
% 1.19/1.38      ((((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F)))
% 1.19/1.38         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.19/1.38      inference('demod', [status(thm)],
% 1.19/1.38                ['249', '250', '251', '252', '253', '254', '255', '256', 
% 1.19/1.38                 '257', '258'])).
% 1.19/1.38  thf('260', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 1.19/1.38       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.19/1.38      inference('split', [status(esa)], ['209'])).
% 1.19/1.38  thf('261', plain,
% 1.19/1.38      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.19/1.38         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.19/1.38      inference('sat_resolution*', [status(thm)], ['206', '240', '260'])).
% 1.19/1.38  thf('262', plain, (((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F))),
% 1.19/1.38      inference('simpl_trail', [status(thm)], ['259', '261'])).
% 1.19/1.38  thf('263', plain,
% 1.19/1.38      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.19/1.38      inference('demod', [status(thm)], ['230', '231', '232'])).
% 1.19/1.38  thf('264', plain,
% 1.19/1.38      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 1.19/1.38      inference('demod', [status(thm)], ['242', '262', '263'])).
% 1.19/1.38  thf('265', plain, (~ (v2_struct_0 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('266', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.19/1.38      inference('clc', [status(thm)], ['264', '265'])).
% 1.19/1.38  thf('267', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('268', plain, ((v2_struct_0 @ sk_C)),
% 1.19/1.38      inference('clc', [status(thm)], ['266', '267'])).
% 1.19/1.38  thf('269', plain, ($false), inference('demod', [status(thm)], ['0', '268'])).
% 1.19/1.38  
% 1.19/1.38  % SZS output end Refutation
% 1.19/1.38  
% 1.19/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
