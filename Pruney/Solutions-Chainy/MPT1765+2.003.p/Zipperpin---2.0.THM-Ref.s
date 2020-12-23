%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hCqWJUZ6hA

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 183 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          : 1098 (4939 expanded)
%              Number of equality atoms :   37 (  90 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k3_xboole_0 @ X10 @ ( k10_relat_1 @ X11 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X36 )
      | ( ( k3_tmap_1 @ X35 @ X33 @ X36 @ X34 @ X37 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X33 ) @ X37 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 )
        = ( k7_relat_1 @ X29 @ X32 ) ) ) ),
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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v5_relat_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc22_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
      | ~ ( v5_relat_1 @ X13 @ X15 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['5','31','58'])).

thf('60',plain,
    ( ( ( k10_relat_1 @ sk_E @ sk_F )
     != ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( k10_relat_1 @ sk_E @ sk_F ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','59'])).

thf('61',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,
    ( ( k3_xboole_0 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( k10_relat_1 @ sk_E @ sk_F ) )
    = ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('70',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['60','68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hCqWJUZ6hA
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 91 iterations in 0.039s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(t139_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.51         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (((k10_relat_1 @ (k7_relat_1 @ X11 @ X10) @ X12)
% 0.21/0.51            = (k3_xboole_0 @ X10 @ (k10_relat_1 @ X11 @ X12)))
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.51  thf(t76_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                         ( v1_funct_2 @
% 0.21/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                         ( m1_subset_1 @
% 0.21/0.51                           E @ 
% 0.21/0.51                           ( k1_zfmisc_1 @
% 0.21/0.51                             ( k2_zfmisc_1 @
% 0.21/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.51                         ( ![F:$i]:
% 0.21/0.51                           ( ( m1_subset_1 @
% 0.21/0.51                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                             ( ( r1_tarski @
% 0.21/0.51                                 ( k8_relset_1 @
% 0.21/0.51                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                   E @ F ) @ 
% 0.21/0.51                                 ( u1_struct_0 @ C ) ) =>
% 0.21/0.51                               ( ( k8_relset_1 @
% 0.21/0.51                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                   E @ F ) =
% 0.21/0.51                                 ( k8_relset_1 @
% 0.21/0.51                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51                ( l1_pre_topc @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                      ( ![E:$i]:
% 0.21/0.51                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                            ( v1_funct_2 @
% 0.21/0.51                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                            ( m1_subset_1 @
% 0.21/0.51                              E @ 
% 0.21/0.51                              ( k1_zfmisc_1 @
% 0.21/0.51                                ( k2_zfmisc_1 @
% 0.21/0.51                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.51                            ( ![F:$i]:
% 0.21/0.51                              ( ( m1_subset_1 @
% 0.21/0.51                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                                ( ( r1_tarski @
% 0.21/0.51                                    ( k8_relset_1 @
% 0.21/0.51                                      ( u1_struct_0 @ D ) @ 
% 0.21/0.51                                      ( u1_struct_0 @ B ) @ E @ F ) @ 
% 0.21/0.51                                    ( u1_struct_0 @ C ) ) =>
% 0.21/0.51                                  ( ( k8_relset_1 @
% 0.21/0.51                                      ( u1_struct_0 @ D ) @ 
% 0.21/0.51                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.21/0.51                                    ( k8_relset_1 @
% 0.21/0.51                                      ( u1_struct_0 @ C ) @ 
% 0.21/0.51                                      ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t76_tmap_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51         sk_F)
% 0.21/0.51         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.51          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((k10_relat_1 @ sk_E @ sk_F)
% 0.21/0.51         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '4'])).
% 0.21/0.51  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d5_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                         ( v1_funct_2 @
% 0.21/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                         ( m1_subset_1 @
% 0.21/0.51                           E @ 
% 0.21/0.51                           ( k1_zfmisc_1 @
% 0.21/0.51                             ( k2_zfmisc_1 @
% 0.21/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.51                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.51                           ( k2_partfun1 @
% 0.21/0.51                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.51                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X33)
% 0.21/0.51          | ~ (v2_pre_topc @ X33)
% 0.21/0.51          | ~ (l1_pre_topc @ X33)
% 0.21/0.51          | ~ (m1_pre_topc @ X34 @ X35)
% 0.21/0.51          | ~ (m1_pre_topc @ X34 @ X36)
% 0.21/0.51          | ((k3_tmap_1 @ X35 @ X33 @ X36 @ X34 @ X37)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33) @ 
% 0.21/0.51                 X37 @ (u1_struct_0 @ X34)))
% 0.21/0.51          | ~ (m1_subset_1 @ X37 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33))))
% 0.21/0.51          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33))
% 0.21/0.51          | ~ (v1_funct_1 @ X37)
% 0.21/0.51          | ~ (m1_pre_topc @ X36 @ X35)
% 0.21/0.51          | ~ (l1_pre_topc @ X35)
% 0.21/0.51          | ~ (v2_pre_topc @ X35)
% 0.21/0.51          | (v2_struct_0 @ X35))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.51          | ~ (v1_funct_1 @ X29)
% 0.21/0.51          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.51              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '17', '18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.51              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '20'])).
% 0.21/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.51              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.51            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.51        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '24'])).
% 0.21/0.51  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.51            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.51            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.21/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.51         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf(dt_k7_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X19 @ X21)
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('36', plain, ((v5_relat_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf(fc22_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ B ) ) =>
% 0.21/0.51       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.21/0.51         ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((v5_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 0.21/0.51          | ~ (v5_relat_1 @ X13 @ X15)
% 0.21/0.51          | ~ (v1_relat_1 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc22_relat_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_E)
% 0.21/0.51          | (v5_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('41', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (v5_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['38', '41'])).
% 0.21/0.51  thf(d19_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v5_relat_1 @ X4 @ X5)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.21/0.51          | ~ (v1_relat_1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_E)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '44'])).
% 0.21/0.51  thf('46', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 0.21/0.51          (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf(t87_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.21/0.51  thf(t11_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.51           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.21/0.51          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 0.21/0.51          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.21/0.51          | ~ (v1_relat_1 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.51          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.51          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.51  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_E)
% 0.21/0.51          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '53'])).
% 0.21/0.51  thf('55', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.21/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.51          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (k7_relat_1 @ sk_E @ X0) @ X1)
% 0.21/0.51           = (k10_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((k10_relat_1 @ sk_E @ sk_F)
% 0.21/0.51         != (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '31', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((((k10_relat_1 @ sk_E @ sk_F)
% 0.21/0.51          != (k3_xboole_0 @ (u1_struct_0 @ sk_C) @ (k10_relat_1 @ sk_E @ sk_F)))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_E))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((r1_tarski @ 
% 0.21/0.51        (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51         sk_F) @ 
% 0.21/0.51        (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((k3_xboole_0 @ 
% 0.21/0.51         (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51          sk_F) @ 
% 0.21/0.51         (u1_struct_0 @ sk_C))
% 0.21/0.51         = (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            sk_F))),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (((k3_xboole_0 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.51         (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51          sk_F))
% 0.21/0.51         = (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            sk_F))),
% 0.21/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((k3_xboole_0 @ (u1_struct_0 @ sk_C) @ (k10_relat_1 @ sk_E @ sk_F))
% 0.21/0.51         = (k10_relat_1 @ sk_E @ sk_F))),
% 0.21/0.51      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.51  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (((k10_relat_1 @ sk_E @ sk_F) != (k10_relat_1 @ sk_E @ sk_F))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '68', '69'])).
% 0.21/0.51  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
