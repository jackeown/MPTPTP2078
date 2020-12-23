%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tw6sSOOssr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:06 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 238 expanded)
%              Number of leaves         :   44 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          : 1132 (5422 expanded)
%              Number of equality atoms :   35 (  88 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t76_tmap_1,conjecture,(
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
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                           => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F ) @ ( u1_struct_0 @ C ) )
                             => ( ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                             => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F ) @ ( u1_struct_0 @ C ) )
                               => ( ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                  = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tmap_1])).

thf('1',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k8_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k10_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('9',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( m1_pre_topc @ X40 @ X42 )
      | ( ( k3_tmap_1 @ X41 @ X39 @ X42 @ X40 @ X43 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X39 ) @ X43 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12','17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_E @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('62',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['41','42'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k8_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k10_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['5','31','65'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_E @ sk_F )
     != ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( k10_relat_1 @ sk_E @ sk_F ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','66'])).

thf('68',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('70',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) )
    = ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( k10_relat_1 @ sk_E @ sk_F ) )
    = ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['41','42'])).

thf('76',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['67','74','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tw6sSOOssr
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 20:46:50 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.46/1.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.46/1.70  % Solved by: fo/fo7.sh
% 1.46/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.70  % done 1198 iterations in 1.251s
% 1.46/1.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.46/1.70  % SZS output start Refutation
% 1.46/1.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.46/1.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.46/1.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.46/1.70  thf(sk_E_type, type, sk_E: $i).
% 1.46/1.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.46/1.70  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.46/1.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.46/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.70  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.46/1.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.46/1.70  thf(sk_F_type, type, sk_F: $i).
% 1.46/1.70  thf(sk_D_type, type, sk_D: $i).
% 1.46/1.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.46/1.70  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.46/1.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.46/1.70  thf(sk_C_type, type, sk_C: $i).
% 1.46/1.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.46/1.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.46/1.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.46/1.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.46/1.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.46/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.46/1.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.46/1.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.46/1.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.46/1.70  thf(t139_funct_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ C ) =>
% 1.46/1.70       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.46/1.70         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.46/1.70  thf('0', plain,
% 1.46/1.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.46/1.70         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 1.46/1.70            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 1.46/1.70          | ~ (v1_relat_1 @ X23))),
% 1.46/1.70      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.46/1.70  thf(t76_tmap_1, conjecture,
% 1.46/1.70    (![A:$i]:
% 1.46/1.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.46/1.70       ( ![B:$i]:
% 1.46/1.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.46/1.70             ( l1_pre_topc @ B ) ) =>
% 1.46/1.70           ( ![C:$i]:
% 1.46/1.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.46/1.70               ( ![D:$i]:
% 1.46/1.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.46/1.70                   ( ![E:$i]:
% 1.46/1.70                     ( ( ( v1_funct_1 @ E ) & 
% 1.46/1.70                         ( v1_funct_2 @
% 1.46/1.70                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.46/1.70                         ( m1_subset_1 @
% 1.46/1.70                           E @ 
% 1.46/1.70                           ( k1_zfmisc_1 @
% 1.46/1.70                             ( k2_zfmisc_1 @
% 1.46/1.70                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.46/1.70                       ( ( m1_pre_topc @ C @ D ) =>
% 1.46/1.70                         ( ![F:$i]:
% 1.46/1.70                           ( ( m1_subset_1 @
% 1.46/1.70                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.46/1.70                             ( ( r1_tarski @
% 1.46/1.70                                 ( k8_relset_1 @
% 1.46/1.70                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 1.46/1.70                                   E @ F ) @ 
% 1.46/1.70                                 ( u1_struct_0 @ C ) ) =>
% 1.46/1.70                               ( ( k8_relset_1 @
% 1.46/1.70                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 1.46/1.70                                   E @ F ) =
% 1.46/1.70                                 ( k8_relset_1 @
% 1.46/1.70                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.46/1.70                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.46/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.70    (~( ![A:$i]:
% 1.46/1.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.46/1.70            ( l1_pre_topc @ A ) ) =>
% 1.46/1.70          ( ![B:$i]:
% 1.46/1.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.46/1.70                ( l1_pre_topc @ B ) ) =>
% 1.46/1.70              ( ![C:$i]:
% 1.46/1.70                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.46/1.70                  ( ![D:$i]:
% 1.46/1.70                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.46/1.70                      ( ![E:$i]:
% 1.46/1.70                        ( ( ( v1_funct_1 @ E ) & 
% 1.46/1.70                            ( v1_funct_2 @
% 1.46/1.70                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.46/1.70                            ( m1_subset_1 @
% 1.46/1.70                              E @ 
% 1.46/1.70                              ( k1_zfmisc_1 @
% 1.46/1.70                                ( k2_zfmisc_1 @
% 1.46/1.70                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.46/1.70                          ( ( m1_pre_topc @ C @ D ) =>
% 1.46/1.70                            ( ![F:$i]:
% 1.46/1.70                              ( ( m1_subset_1 @
% 1.46/1.70                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.46/1.70                                ( ( r1_tarski @
% 1.46/1.70                                    ( k8_relset_1 @
% 1.46/1.70                                      ( u1_struct_0 @ D ) @ 
% 1.46/1.70                                      ( u1_struct_0 @ B ) @ E @ F ) @ 
% 1.46/1.70                                    ( u1_struct_0 @ C ) ) =>
% 1.46/1.70                                  ( ( k8_relset_1 @
% 1.46/1.70                                      ( u1_struct_0 @ D ) @ 
% 1.46/1.70                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 1.46/1.70                                    ( k8_relset_1 @
% 1.46/1.70                                      ( u1_struct_0 @ C ) @ 
% 1.46/1.70                                      ( u1_struct_0 @ B ) @ 
% 1.46/1.70                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.46/1.70    inference('cnf.neg', [status(esa)], [t76_tmap_1])).
% 1.46/1.70  thf('1', plain,
% 1.46/1.70      (((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.46/1.70         sk_F)
% 1.46/1.70         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.46/1.70             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('2', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_E @ 
% 1.46/1.70        (k1_zfmisc_1 @ 
% 1.46/1.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(redefinition_k8_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.70       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.46/1.70  thf('3', plain,
% 1.46/1.70      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.46/1.70          | ((k8_relset_1 @ X29 @ X30 @ X28 @ X31) = (k10_relat_1 @ X28 @ X31)))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.46/1.70  thf('4', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.46/1.70           X0) = (k10_relat_1 @ sk_E @ X0))),
% 1.46/1.70      inference('sup-', [status(thm)], ['2', '3'])).
% 1.46/1.70  thf('5', plain,
% 1.46/1.70      (((k10_relat_1 @ sk_E @ sk_F)
% 1.46/1.70         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.46/1.70             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 1.46/1.70      inference('demod', [status(thm)], ['1', '4'])).
% 1.46/1.70  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('8', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_E @ 
% 1.46/1.70        (k1_zfmisc_1 @ 
% 1.46/1.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(d5_tmap_1, axiom,
% 1.46/1.70    (![A:$i]:
% 1.46/1.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.46/1.70       ( ![B:$i]:
% 1.46/1.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.46/1.70             ( l1_pre_topc @ B ) ) =>
% 1.46/1.70           ( ![C:$i]:
% 1.46/1.70             ( ( m1_pre_topc @ C @ A ) =>
% 1.46/1.70               ( ![D:$i]:
% 1.46/1.70                 ( ( m1_pre_topc @ D @ A ) =>
% 1.46/1.70                   ( ![E:$i]:
% 1.46/1.70                     ( ( ( v1_funct_1 @ E ) & 
% 1.46/1.70                         ( v1_funct_2 @
% 1.46/1.70                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.46/1.70                         ( m1_subset_1 @
% 1.46/1.70                           E @ 
% 1.46/1.70                           ( k1_zfmisc_1 @
% 1.46/1.70                             ( k2_zfmisc_1 @
% 1.46/1.70                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.46/1.70                       ( ( m1_pre_topc @ D @ C ) =>
% 1.46/1.70                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.46/1.70                           ( k2_partfun1 @
% 1.46/1.70                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.46/1.70                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.46/1.70  thf('9', plain,
% 1.46/1.70      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.46/1.70         ((v2_struct_0 @ X39)
% 1.46/1.70          | ~ (v2_pre_topc @ X39)
% 1.46/1.70          | ~ (l1_pre_topc @ X39)
% 1.46/1.70          | ~ (m1_pre_topc @ X40 @ X41)
% 1.46/1.70          | ~ (m1_pre_topc @ X40 @ X42)
% 1.46/1.70          | ((k3_tmap_1 @ X41 @ X39 @ X42 @ X40 @ X43)
% 1.46/1.70              = (k2_partfun1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X39) @ 
% 1.46/1.70                 X43 @ (u1_struct_0 @ X40)))
% 1.46/1.70          | ~ (m1_subset_1 @ X43 @ 
% 1.46/1.70               (k1_zfmisc_1 @ 
% 1.46/1.70                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X39))))
% 1.46/1.70          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X39))
% 1.46/1.70          | ~ (v1_funct_1 @ X43)
% 1.46/1.70          | ~ (m1_pre_topc @ X42 @ X41)
% 1.46/1.70          | ~ (l1_pre_topc @ X41)
% 1.46/1.70          | ~ (v2_pre_topc @ X41)
% 1.46/1.70          | (v2_struct_0 @ X41))),
% 1.46/1.70      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.46/1.70  thf('10', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i]:
% 1.46/1.70         ((v2_struct_0 @ X0)
% 1.46/1.70          | ~ (v2_pre_topc @ X0)
% 1.46/1.70          | ~ (l1_pre_topc @ X0)
% 1.46/1.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.46/1.70          | ~ (v1_funct_1 @ sk_E)
% 1.46/1.70          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.46/1.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.46/1.70              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.46/1.70                 sk_E @ (u1_struct_0 @ X1)))
% 1.46/1.70          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.46/1.70          | ~ (m1_pre_topc @ X1 @ X0)
% 1.46/1.70          | ~ (l1_pre_topc @ sk_B)
% 1.46/1.70          | ~ (v2_pre_topc @ sk_B)
% 1.46/1.70          | (v2_struct_0 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['8', '9'])).
% 1.46/1.70  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('12', plain,
% 1.46/1.70      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('13', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_E @ 
% 1.46/1.70        (k1_zfmisc_1 @ 
% 1.46/1.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(redefinition_k2_partfun1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.70     ( ( ( v1_funct_1 @ C ) & 
% 1.46/1.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.46/1.70       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.46/1.70  thf('14', plain,
% 1.46/1.70      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.46/1.70          | ~ (v1_funct_1 @ X35)
% 1.46/1.70          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.46/1.70  thf('15', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.46/1.70            X0) = (k7_relat_1 @ sk_E @ X0))
% 1.46/1.70          | ~ (v1_funct_1 @ sk_E))),
% 1.46/1.70      inference('sup-', [status(thm)], ['13', '14'])).
% 1.46/1.70  thf('16', plain, ((v1_funct_1 @ sk_E)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('17', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.46/1.70           X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.46/1.70      inference('demod', [status(thm)], ['15', '16'])).
% 1.46/1.70  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('20', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i]:
% 1.46/1.70         ((v2_struct_0 @ X0)
% 1.46/1.70          | ~ (v2_pre_topc @ X0)
% 1.46/1.70          | ~ (l1_pre_topc @ X0)
% 1.46/1.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.46/1.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.46/1.70              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 1.46/1.70          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.46/1.70          | ~ (m1_pre_topc @ X1 @ X0)
% 1.46/1.70          | (v2_struct_0 @ sk_B))),
% 1.46/1.70      inference('demod', [status(thm)], ['10', '11', '12', '17', '18', '19'])).
% 1.46/1.70  thf('21', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((v2_struct_0 @ sk_B)
% 1.46/1.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.46/1.70          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.46/1.70          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 1.46/1.70              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.46/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.46/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.46/1.70          | (v2_struct_0 @ sk_A))),
% 1.46/1.70      inference('sup-', [status(thm)], ['7', '20'])).
% 1.46/1.70  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('24', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((v2_struct_0 @ sk_B)
% 1.46/1.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.46/1.70          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.46/1.70          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 1.46/1.70              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.46/1.70          | (v2_struct_0 @ sk_A))),
% 1.46/1.70      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.46/1.70  thf('25', plain,
% 1.46/1.70      (((v2_struct_0 @ sk_A)
% 1.46/1.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.46/1.70            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.46/1.70        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.46/1.70        | (v2_struct_0 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['6', '24'])).
% 1.46/1.70  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('27', plain,
% 1.46/1.70      (((v2_struct_0 @ sk_A)
% 1.46/1.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.46/1.70            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.46/1.70        | (v2_struct_0 @ sk_B))),
% 1.46/1.70      inference('demod', [status(thm)], ['25', '26'])).
% 1.46/1.70  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('29', plain,
% 1.46/1.70      (((v2_struct_0 @ sk_B)
% 1.46/1.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.46/1.70            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.46/1.70      inference('clc', [status(thm)], ['27', '28'])).
% 1.46/1.70  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('31', plain,
% 1.46/1.70      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.46/1.70         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.46/1.70      inference('clc', [status(thm)], ['29', '30'])).
% 1.46/1.70  thf('32', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_E @ 
% 1.46/1.70        (k1_zfmisc_1 @ 
% 1.46/1.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(t3_subset, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.46/1.70  thf('33', plain,
% 1.46/1.70      (![X7 : $i, X8 : $i]:
% 1.46/1.70         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.46/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.46/1.70  thf('34', plain,
% 1.46/1.70      ((r1_tarski @ sk_E @ 
% 1.46/1.70        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['32', '33'])).
% 1.46/1.70  thf(t88_relat_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 1.46/1.70  thf('35', plain,
% 1.46/1.70      (![X20 : $i, X21 : $i]:
% 1.46/1.70         ((r1_tarski @ (k7_relat_1 @ X20 @ X21) @ X20) | ~ (v1_relat_1 @ X20))),
% 1.46/1.70      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.46/1.70  thf(t1_xboole_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i]:
% 1.46/1.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.46/1.70       ( r1_tarski @ A @ C ) ))).
% 1.46/1.70  thf('36', plain,
% 1.46/1.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.46/1.70         (~ (r1_tarski @ X2 @ X3)
% 1.46/1.70          | ~ (r1_tarski @ X3 @ X4)
% 1.46/1.70          | (r1_tarski @ X2 @ X4))),
% 1.46/1.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.46/1.70  thf('37', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         (~ (v1_relat_1 @ X0)
% 1.46/1.70          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 1.46/1.70          | ~ (r1_tarski @ X0 @ X2))),
% 1.46/1.70      inference('sup-', [status(thm)], ['35', '36'])).
% 1.46/1.70  thf('38', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((r1_tarski @ (k7_relat_1 @ sk_E @ X0) @ 
% 1.46/1.70           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.46/1.70          | ~ (v1_relat_1 @ sk_E))),
% 1.46/1.70      inference('sup-', [status(thm)], ['34', '37'])).
% 1.46/1.70  thf('39', plain,
% 1.46/1.70      ((m1_subset_1 @ sk_E @ 
% 1.46/1.70        (k1_zfmisc_1 @ 
% 1.46/1.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf(cc2_relat_1, axiom,
% 1.46/1.70    (![A:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ A ) =>
% 1.46/1.70       ( ![B:$i]:
% 1.46/1.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.46/1.70  thf('40', plain,
% 1.46/1.70      (![X10 : $i, X11 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.46/1.70          | (v1_relat_1 @ X10)
% 1.46/1.70          | ~ (v1_relat_1 @ X11))),
% 1.46/1.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.46/1.70  thf('41', plain,
% 1.46/1.70      ((~ (v1_relat_1 @ 
% 1.46/1.70           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.46/1.70        | (v1_relat_1 @ sk_E))),
% 1.46/1.70      inference('sup-', [status(thm)], ['39', '40'])).
% 1.46/1.70  thf(fc6_relat_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.46/1.70  thf('42', plain,
% 1.46/1.70      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 1.46/1.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.46/1.70  thf('43', plain, ((v1_relat_1 @ sk_E)),
% 1.46/1.70      inference('demod', [status(thm)], ['41', '42'])).
% 1.46/1.70  thf('44', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (r1_tarski @ (k7_relat_1 @ sk_E @ X0) @ 
% 1.46/1.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.46/1.70      inference('demod', [status(thm)], ['38', '43'])).
% 1.46/1.70  thf('45', plain,
% 1.46/1.70      (![X7 : $i, X9 : $i]:
% 1.46/1.70         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.46/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.46/1.70  thf('46', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 1.46/1.70          (k1_zfmisc_1 @ 
% 1.46/1.70           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('sup-', [status(thm)], ['44', '45'])).
% 1.46/1.70  thf(cc2_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i]:
% 1.46/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.46/1.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.46/1.70  thf('47', plain,
% 1.46/1.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.46/1.70         ((v5_relat_1 @ X25 @ X27)
% 1.46/1.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.46/1.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.46/1.70  thf('48', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (v5_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ (u1_struct_0 @ sk_B))),
% 1.46/1.70      inference('sup-', [status(thm)], ['46', '47'])).
% 1.46/1.70  thf(d19_relat_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ B ) =>
% 1.46/1.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.46/1.70  thf('49', plain,
% 1.46/1.70      (![X12 : $i, X13 : $i]:
% 1.46/1.70         (~ (v5_relat_1 @ X12 @ X13)
% 1.46/1.70          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 1.46/1.70          | ~ (v1_relat_1 @ X12))),
% 1.46/1.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.46/1.70  thf('50', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 1.46/1.70          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 1.46/1.70             (u1_struct_0 @ sk_B)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['48', '49'])).
% 1.46/1.70  thf('51', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 1.46/1.70          (k1_zfmisc_1 @ 
% 1.46/1.70           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('sup-', [status(thm)], ['44', '45'])).
% 1.46/1.70  thf('52', plain,
% 1.46/1.70      (![X10 : $i, X11 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.46/1.70          | (v1_relat_1 @ X10)
% 1.46/1.70          | ~ (v1_relat_1 @ X11))),
% 1.46/1.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.46/1.70  thf('53', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (~ (v1_relat_1 @ 
% 1.46/1.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.46/1.70          | (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 1.46/1.70      inference('sup-', [status(thm)], ['51', '52'])).
% 1.46/1.70  thf('54', plain,
% 1.46/1.70      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 1.46/1.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.46/1.70  thf('55', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 1.46/1.70      inference('demod', [status(thm)], ['53', '54'])).
% 1.46/1.70  thf('56', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 1.46/1.70          (u1_struct_0 @ sk_B))),
% 1.46/1.70      inference('demod', [status(thm)], ['50', '55'])).
% 1.46/1.70  thf(t87_relat_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ B ) =>
% 1.46/1.70       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.46/1.70  thf('57', plain,
% 1.46/1.70      (![X18 : $i, X19 : $i]:
% 1.46/1.70         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ X19)
% 1.46/1.70          | ~ (v1_relat_1 @ X18))),
% 1.46/1.70      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.46/1.70  thf(t11_relset_1, axiom,
% 1.46/1.70    (![A:$i,B:$i,C:$i]:
% 1.46/1.70     ( ( v1_relat_1 @ C ) =>
% 1.46/1.70       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.46/1.70           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.46/1.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.46/1.70  thf('58', plain,
% 1.46/1.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.46/1.70         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 1.46/1.70          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 1.46/1.70          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.46/1.70          | ~ (v1_relat_1 @ X32))),
% 1.46/1.70      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.46/1.70  thf('59', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.70         (~ (v1_relat_1 @ X1)
% 1.46/1.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.46/1.70          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.46/1.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 1.46/1.70          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 1.46/1.70      inference('sup-', [status(thm)], ['57', '58'])).
% 1.46/1.70  thf('60', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 1.46/1.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 1.46/1.70          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 1.46/1.70          | ~ (v1_relat_1 @ sk_E))),
% 1.46/1.70      inference('sup-', [status(thm)], ['56', '59'])).
% 1.46/1.70  thf('61', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 1.46/1.70      inference('demod', [status(thm)], ['53', '54'])).
% 1.46/1.70  thf('62', plain, ((v1_relat_1 @ sk_E)),
% 1.46/1.70      inference('demod', [status(thm)], ['41', '42'])).
% 1.46/1.70  thf('63', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 1.46/1.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 1.46/1.70      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.46/1.70  thf('64', plain,
% 1.46/1.70      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.46/1.70         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.46/1.70          | ((k8_relset_1 @ X29 @ X30 @ X28 @ X31) = (k10_relat_1 @ X28 @ X31)))),
% 1.46/1.70      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.46/1.70  thf('65', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i]:
% 1.46/1.70         ((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 1.46/1.70           (k7_relat_1 @ sk_E @ X0) @ X1)
% 1.46/1.70           = (k10_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ X1))),
% 1.46/1.70      inference('sup-', [status(thm)], ['63', '64'])).
% 1.46/1.70  thf('66', plain,
% 1.46/1.70      (((k10_relat_1 @ sk_E @ sk_F)
% 1.46/1.70         != (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 1.46/1.70      inference('demod', [status(thm)], ['5', '31', '65'])).
% 1.46/1.70  thf('67', plain,
% 1.46/1.70      ((((k10_relat_1 @ sk_E @ sk_F)
% 1.46/1.70          != (k3_xboole_0 @ (u1_struct_0 @ sk_C) @ (k10_relat_1 @ sk_E @ sk_F)))
% 1.46/1.70        | ~ (v1_relat_1 @ sk_E))),
% 1.46/1.70      inference('sup-', [status(thm)], ['0', '66'])).
% 1.46/1.70  thf('68', plain,
% 1.46/1.70      ((r1_tarski @ 
% 1.46/1.70        (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.46/1.70         sk_F) @ 
% 1.46/1.70        (u1_struct_0 @ sk_C))),
% 1.46/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.70  thf('69', plain,
% 1.46/1.70      (![X0 : $i]:
% 1.46/1.70         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.46/1.70           X0) = (k10_relat_1 @ sk_E @ X0))),
% 1.46/1.70      inference('sup-', [status(thm)], ['2', '3'])).
% 1.46/1.70  thf('70', plain,
% 1.46/1.70      ((r1_tarski @ (k10_relat_1 @ sk_E @ sk_F) @ (u1_struct_0 @ sk_C))),
% 1.46/1.70      inference('demod', [status(thm)], ['68', '69'])).
% 1.46/1.70  thf(t28_xboole_1, axiom,
% 1.46/1.70    (![A:$i,B:$i]:
% 1.46/1.70     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.46/1.70  thf('71', plain,
% 1.46/1.70      (![X5 : $i, X6 : $i]:
% 1.46/1.70         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 1.46/1.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.46/1.70  thf('72', plain,
% 1.46/1.70      (((k3_xboole_0 @ (k10_relat_1 @ sk_E @ sk_F) @ (u1_struct_0 @ sk_C))
% 1.46/1.70         = (k10_relat_1 @ sk_E @ sk_F))),
% 1.46/1.70      inference('sup-', [status(thm)], ['70', '71'])).
% 1.46/1.70  thf(commutativity_k3_xboole_0, axiom,
% 1.46/1.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.46/1.70  thf('73', plain,
% 1.46/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.46/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.46/1.70  thf('74', plain,
% 1.46/1.70      (((k3_xboole_0 @ (u1_struct_0 @ sk_C) @ (k10_relat_1 @ sk_E @ sk_F))
% 1.46/1.70         = (k10_relat_1 @ sk_E @ sk_F))),
% 1.46/1.70      inference('demod', [status(thm)], ['72', '73'])).
% 1.46/1.70  thf('75', plain, ((v1_relat_1 @ sk_E)),
% 1.46/1.70      inference('demod', [status(thm)], ['41', '42'])).
% 1.46/1.70  thf('76', plain,
% 1.46/1.70      (((k10_relat_1 @ sk_E @ sk_F) != (k10_relat_1 @ sk_E @ sk_F))),
% 1.46/1.70      inference('demod', [status(thm)], ['67', '74', '75'])).
% 1.46/1.70  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 1.46/1.70  
% 1.46/1.70  % SZS output end Refutation
% 1.46/1.70  
% 1.55/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
