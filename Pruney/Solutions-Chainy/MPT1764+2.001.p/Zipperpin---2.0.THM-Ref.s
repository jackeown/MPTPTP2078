%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vYgDt8pdVj

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:04 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 223 expanded)
%              Number of leaves         :   36 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          : 1297 (7007 expanded)
%              Number of equality atoms :   37 ( 121 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t75_tmap_1,conjecture,(
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
                           => ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k7_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                             => ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                               => ( ( k7_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                  = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tmap_1])).

thf('0',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
        = ( k9_relat_1 @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( ( k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) @ X27 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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
    inference(demod,[status(thm)],['12','13','14','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k2_tmap_1 @ X21 @ X19 @ X22 @ X20 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X22 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('41',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','44','49','50','51','52','53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['7','33','84'])).

thf('86',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_F )
     != ( k9_relat_1 @ sk_E @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('88',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vYgDt8pdVj
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 73 iterations in 0.044s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(t75_tmap_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.50                   ( ![E:$i]:
% 0.19/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                         ( v1_funct_2 @
% 0.19/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                         ( m1_subset_1 @
% 0.19/0.50                           E @ 
% 0.19/0.50                           ( k1_zfmisc_1 @
% 0.19/0.50                             ( k2_zfmisc_1 @
% 0.19/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                       ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.50                         ( ![F:$i]:
% 0.19/0.50                           ( ( m1_subset_1 @
% 0.19/0.50                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.19/0.50                             ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.50                               ( ( k7_relset_1 @
% 0.19/0.50                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                   E @ F ) =
% 0.19/0.50                                 ( k7_relset_1 @
% 0.19/0.50                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.50            ( l1_pre_topc @ A ) ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50                ( l1_pre_topc @ B ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.50                  ( ![D:$i]:
% 0.19/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.50                      ( ![E:$i]:
% 0.19/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                            ( v1_funct_2 @
% 0.19/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                            ( m1_subset_1 @
% 0.19/0.50                              E @ 
% 0.19/0.50                              ( k1_zfmisc_1 @
% 0.19/0.50                                ( k2_zfmisc_1 @
% 0.19/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                          ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.50                            ( ![F:$i]:
% 0.19/0.50                              ( ( m1_subset_1 @
% 0.19/0.50                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.19/0.50                                ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.50                                  ( ( k7_relset_1 @
% 0.19/0.50                                      ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.19/0.50                                    ( k7_relset_1 @
% 0.19/0.50                                      ( u1_struct_0 @ C ) @ 
% 0.19/0.50                                      ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t75_tmap_1])).
% 0.19/0.50  thf('0', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t162_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i,C:$i]:
% 0.19/0.50         ( ( r1_tarski @ B @ C ) =>
% 0.19/0.50           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.19/0.50             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.50          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.19/0.50              = (k9_relat_1 @ X2 @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X0)
% 0.19/0.50          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 0.19/0.50              = (k9_relat_1 @ X0 @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50         sk_F)
% 0.19/0.50         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.19/0.50          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50           X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (((k9_relat_1 @ sk_E @ sk_F)
% 0.19/0.50         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.50  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d5_tmap_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.50                   ( ![E:$i]:
% 0.19/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                         ( v1_funct_2 @
% 0.19/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                         ( m1_subset_1 @
% 0.19/0.50                           E @ 
% 0.19/0.50                           ( k1_zfmisc_1 @
% 0.19/0.50                             ( k2_zfmisc_1 @
% 0.19/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.50                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.50                           ( k2_partfun1 @
% 0.19/0.50                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.50                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X23)
% 0.19/0.50          | ~ (v2_pre_topc @ X23)
% 0.19/0.50          | ~ (l1_pre_topc @ X23)
% 0.19/0.50          | ~ (m1_pre_topc @ X24 @ X25)
% 0.19/0.50          | ~ (m1_pre_topc @ X24 @ X26)
% 0.19/0.50          | ((k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23) @ 
% 0.19/0.50                 X27 @ (u1_struct_0 @ X24)))
% 0.19/0.50          | ~ (m1_subset_1 @ X27 @ 
% 0.19/0.50               (k1_zfmisc_1 @ 
% 0.19/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))))
% 0.19/0.50          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))
% 0.19/0.50          | ~ (v1_funct_1 @ X27)
% 0.19/0.50          | ~ (m1_pre_topc @ X26 @ X25)
% 0.19/0.50          | ~ (l1_pre_topc @ X25)
% 0.19/0.50          | ~ (v2_pre_topc @ X25)
% 0.19/0.50          | (v2_struct_0 @ X25))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k2_partfun1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.50       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.19/0.50          | ~ (v1_funct_1 @ X10)
% 0.19/0.50          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.50  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.50          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.19/0.50              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['12', '13', '14', '19', '20', '21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_B)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.50              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '22'])).
% 0.19/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_B)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.50              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_A)
% 0.19/0.50        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.50            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.50        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.50        | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '26'])).
% 0.19/0.50  thf('28', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_A)
% 0.19/0.50        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.50            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.50        | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_B)
% 0.19/0.50        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.50            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.19/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.50         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf(dt_l1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d4_tmap_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                 ( m1_subset_1 @
% 0.19/0.50                   C @ 
% 0.19/0.50                   ( k1_zfmisc_1 @
% 0.19/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k2_partfun1 @
% 0.19/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X19)
% 0.19/0.50          | ~ (v2_pre_topc @ X19)
% 0.19/0.50          | ~ (l1_pre_topc @ X19)
% 0.19/0.50          | ~ (m1_pre_topc @ X20 @ X21)
% 0.19/0.50          | ((k2_tmap_1 @ X21 @ X19 @ X22 @ X20)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ 
% 0.19/0.50                 X22 @ (u1_struct_0 @ X20)))
% 0.19/0.50          | ~ (m1_subset_1 @ X22 @ 
% 0.19/0.50               (k1_zfmisc_1 @ 
% 0.19/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.19/0.50          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.19/0.50          | ~ (v1_funct_1 @ X22)
% 0.19/0.50          | ~ (l1_pre_topc @ X21)
% 0.19/0.50          | ~ (v2_pre_topc @ X21)
% 0.19/0.50          | (v2_struct_0 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_D)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.19/0.50          | (v2_pre_topc @ X14)
% 0.19/0.50          | ~ (l1_pre_topc @ X15)
% 0.19/0.50          | ~ (v2_pre_topc @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('44', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.19/0.50  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_m1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X17 @ X18)
% 0.19/0.50          | (l1_pre_topc @ X17)
% 0.19/0.50          | ~ (l1_pre_topc @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.50  thf('47', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.50  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_D)
% 0.19/0.50          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.19/0.50              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)],
% 0.19/0.50                ['38', '44', '49', '50', '51', '52', '53', '54'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_B)
% 0.19/0.50        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.19/0.50            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.50        | (v2_struct_0 @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '55'])).
% 0.19/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_D)
% 0.19/0.50        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.19/0.50            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.19/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.19/0.50  thf('59', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.19/0.50         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['58', '59'])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_k2_tmap_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.19/0.50         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50         ( m1_subset_1 @
% 0.19/0.50           C @ 
% 0.19/0.50           ( k1_zfmisc_1 @
% 0.19/0.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.19/0.50         ( l1_struct_0 @ D ) ) =>
% 0.19/0.50       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.50         ( v1_funct_2 @
% 0.19/0.50           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.19/0.50           ( u1_struct_0 @ B ) ) & 
% 0.19/0.50         ( m1_subset_1 @
% 0.19/0.50           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.19/0.50           ( k1_zfmisc_1 @
% 0.19/0.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X28 @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 0.19/0.50          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 0.19/0.50          | ~ (v1_funct_1 @ X28)
% 0.19/0.50          | ~ (l1_struct_0 @ X30)
% 0.19/0.50          | ~ (l1_struct_0 @ X29)
% 0.19/0.50          | ~ (l1_struct_0 @ X31)
% 0.19/0.50          | (m1_subset_1 @ (k2_tmap_1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30)))))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.19/0.50           (k1_zfmisc_1 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50          | ~ (l1_struct_0 @ X0)
% 0.19/0.50          | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50          | ~ (l1_struct_0 @ sk_B)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.50  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('68', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.19/0.50           (k1_zfmisc_1 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50          | ~ (l1_struct_0 @ X0)
% 0.19/0.50          | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50          | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.19/0.50  thf('69', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ sk_D)
% 0.19/0.50          | ~ (l1_struct_0 @ sk_B)
% 0.19/0.50          | ~ (l1_struct_0 @ X0)
% 0.19/0.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['62', '68'])).
% 0.19/0.50  thf('70', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('71', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ sk_B)
% 0.19/0.50          | ~ (l1_struct_0 @ X0)
% 0.19/0.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.19/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.50  thf('72', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ sk_B)
% 0.19/0.50          | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50          | ~ (l1_struct_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['61', '71'])).
% 0.19/0.50  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('74', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.19/0.50           (k1_zfmisc_1 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50          | ~ (l1_struct_0 @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.50  thf('75', plain,
% 0.19/0.50      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.19/0.50         (k1_zfmisc_1 @ 
% 0.19/0.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50        | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.50      inference('sup+', [status(thm)], ['60', '74'])).
% 0.19/0.50  thf('76', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_C)
% 0.19/0.50        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.19/0.50           (k1_zfmisc_1 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '75'])).
% 0.19/0.50  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('78', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X17 @ X18)
% 0.19/0.50          | (l1_pre_topc @ X17)
% 0.19/0.50          | ~ (l1_pre_topc @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.50  thf('79', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.19/0.50  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('81', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.50  thf('82', plain,
% 0.19/0.50      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['76', '81'])).
% 0.19/0.50  thf('83', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.19/0.50          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.50  thf('84', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0)
% 0.19/0.50           = (k9_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.19/0.50  thf('85', plain,
% 0.19/0.50      (((k9_relat_1 @ sk_E @ sk_F)
% 0.19/0.50         != (k9_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '33', '84'])).
% 0.19/0.50  thf('86', plain,
% 0.19/0.50      ((((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))
% 0.19/0.50        | ~ (v1_relat_1 @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '85'])).
% 0.19/0.50  thf('87', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc1_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( v1_relat_1 @ C ) ))).
% 0.19/0.50  thf('88', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((v1_relat_1 @ X3)
% 0.19/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.50  thf('89', plain, ((v1_relat_1 @ sk_E)),
% 0.19/0.50      inference('sup-', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('90', plain,
% 0.19/0.50      (((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))),
% 0.19/0.50      inference('demod', [status(thm)], ['86', '89'])).
% 0.19/0.50  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
