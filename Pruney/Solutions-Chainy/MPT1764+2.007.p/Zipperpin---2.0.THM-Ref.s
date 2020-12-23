%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.scI1bq4RfU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:05 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 177 expanded)
%              Number of leaves         :   38 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          : 1137 (4659 expanded)
%              Number of equality atoms :   33 (  87 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X11 @ X10 ) @ X9 )
        = ( k9_relat_1 @ X11 @ X9 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 )
        = ( k7_relat_1 @ X29 @ X32 ) ) ) ),
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

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X26 @ X27 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ( v1_relat_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X24 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['40','64'])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['7','33','67'])).

thf('69',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_F )
     != ( k9_relat_1 @ sk_E @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['61','62'])).

thf('71',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.scI1bq4RfU
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 325 iterations in 0.227s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.68  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.68  thf(t75_tmap_1, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.68             ( l1_pre_topc @ B ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.68               ( ![D:$i]:
% 0.45/0.68                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.68                   ( ![E:$i]:
% 0.45/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.68                         ( v1_funct_2 @
% 0.45/0.68                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                         ( m1_subset_1 @
% 0.45/0.68                           E @ 
% 0.45/0.68                           ( k1_zfmisc_1 @
% 0.45/0.68                             ( k2_zfmisc_1 @
% 0.45/0.68                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68                       ( ( m1_pre_topc @ C @ D ) =>
% 0.45/0.68                         ( ![F:$i]:
% 0.45/0.68                           ( ( m1_subset_1 @
% 0.45/0.68                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.45/0.68                             ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.68                               ( ( k7_relset_1 @
% 0.45/0.68                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.68                                   E @ F ) =
% 0.45/0.68                                 ( k7_relset_1 @
% 0.45/0.68                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.68                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.68            ( l1_pre_topc @ A ) ) =>
% 0.45/0.68          ( ![B:$i]:
% 0.45/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.68                ( l1_pre_topc @ B ) ) =>
% 0.45/0.68              ( ![C:$i]:
% 0.45/0.68                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.68                  ( ![D:$i]:
% 0.45/0.68                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.68                      ( ![E:$i]:
% 0.45/0.68                        ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.68                            ( v1_funct_2 @
% 0.45/0.68                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                            ( m1_subset_1 @
% 0.45/0.68                              E @ 
% 0.45/0.68                              ( k1_zfmisc_1 @
% 0.45/0.68                                ( k2_zfmisc_1 @
% 0.45/0.68                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68                          ( ( m1_pre_topc @ C @ D ) =>
% 0.45/0.68                            ( ![F:$i]:
% 0.45/0.68                              ( ( m1_subset_1 @
% 0.45/0.68                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.45/0.68                                ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.68                                  ( ( k7_relset_1 @
% 0.45/0.68                                      ( u1_struct_0 @ D ) @ 
% 0.45/0.68                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.45/0.68                                    ( k7_relset_1 @
% 0.45/0.68                                      ( u1_struct_0 @ C ) @ 
% 0.45/0.68                                      ( u1_struct_0 @ B ) @ 
% 0.45/0.68                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t75_tmap_1])).
% 0.45/0.68  thf('0', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t162_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ![B:$i,C:$i]:
% 0.45/0.68         ( ( r1_tarski @ B @ C ) =>
% 0.45/0.68           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.45/0.68             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X9 @ X10)
% 0.45/0.68          | ((k9_relat_1 @ (k7_relat_1 @ X11 @ X10) @ X9)
% 0.45/0.68              = (k9_relat_1 @ X11 @ X9))
% 0.45/0.68          | ~ (v1_relat_1 @ X11))),
% 0.45/0.68      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X0)
% 0.45/0.68          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 0.45/0.68              = (k9_relat_1 @ X0 @ sk_F)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68         sk_F)
% 0.45/0.68         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_E @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.45/0.68          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (((k9_relat_1 @ sk_E @ sk_F)
% 0.45/0.68         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.68  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_E @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(d5_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.68             ( l1_pre_topc @ B ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( m1_pre_topc @ C @ A ) =>
% 0.45/0.68               ( ![D:$i]:
% 0.45/0.68                 ( ( m1_pre_topc @ D @ A ) =>
% 0.45/0.68                   ( ![E:$i]:
% 0.45/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.68                         ( v1_funct_2 @
% 0.45/0.68                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                         ( m1_subset_1 @
% 0.45/0.68                           E @ 
% 0.45/0.68                           ( k1_zfmisc_1 @
% 0.45/0.68                             ( k2_zfmisc_1 @
% 0.45/0.68                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68                       ( ( m1_pre_topc @ D @ C ) =>
% 0.45/0.68                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.68                           ( k2_partfun1 @
% 0.45/0.68                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.45/0.68                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X33)
% 0.45/0.68          | ~ (v2_pre_topc @ X33)
% 0.45/0.68          | ~ (l1_pre_topc @ X33)
% 0.45/0.68          | ~ (m1_pre_topc @ X34 @ X35)
% 0.45/0.68          | ~ (m1_pre_topc @ X34 @ X36)
% 0.45/0.68          | ((k3_tmap_1 @ X35 @ X33 @ X36 @ X34 @ X37)
% 0.45/0.68              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33) @ 
% 0.45/0.68                 X37 @ (u1_struct_0 @ X34)))
% 0.45/0.68          | ~ (m1_subset_1 @ X37 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33))))
% 0.45/0.68          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33))
% 0.45/0.68          | ~ (v1_funct_1 @ X37)
% 0.45/0.68          | ~ (m1_pre_topc @ X36 @ X35)
% 0.45/0.68          | ~ (l1_pre_topc @ X35)
% 0.45/0.68          | ~ (v2_pre_topc @ X35)
% 0.45/0.68          | (v2_struct_0 @ X35))),
% 0.45/0.68      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X0)
% 0.45/0.68          | ~ (v2_pre_topc @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.68          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.45/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68                 sk_E @ (u1_struct_0 @ X1)))
% 0.45/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.45/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.68          | (v2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_E @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k2_partfun1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.45/0.68          | ~ (v1_funct_1 @ X29)
% 0.45/0.68          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ sk_E))),
% 0.45/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.68  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.68  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X0)
% 0.45/0.68          | ~ (v2_pre_topc @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.45/0.68              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.45/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.45/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.68          | (v2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['12', '13', '14', '19', '20', '21'])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v2_struct_0 @ sk_B)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.45/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.45/0.68              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.45/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68          | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['9', '22'])).
% 0.45/0.68  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v2_struct_0 @ sk_B)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.45/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.45/0.68              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.45/0.68          | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.45/0.68            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.45/0.68        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.45/0.68        | (v2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['8', '26'])).
% 0.45/0.68  thf('28', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.45/0.68            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.45/0.68        | (v2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.68  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_B)
% 0.45/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.45/0.68            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.45/0.68      inference('clc', [status(thm)], ['29', '30'])).
% 0.45/0.68  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.45/0.68         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.45/0.68      inference('clc', [status(thm)], ['31', '32'])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_E @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_k7_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.45/0.68          | (m1_subset_1 @ (k7_relset_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.45/0.68             (k1_zfmisc_1 @ X16)))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (m1_subset_1 @ 
% 0.45/0.68          (k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) @ 
% 0.45/0.68          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.68  thf(t3_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (r1_tarski @ 
% 0.45/0.68          (k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) @ 
% 0.45/0.68          (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_E @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_k2_partfun1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.45/0.68         ( m1_subset_1 @
% 0.45/0.68           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.45/0.68           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.45/0.68          | ~ (v1_funct_1 @ X25)
% 0.45/0.68          | (m1_subset_1 @ (k2_partfun1 @ X26 @ X27 @ X25 @ X28) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ 
% 0.45/0.68           (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68            X0) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68          | ~ (v1_funct_1 @ sk_E))),
% 0.45/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.68  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (m1_subset_1 @ 
% 0.45/0.68          (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) @ 
% 0.45/0.68          (k1_zfmisc_1 @ 
% 0.45/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.68  thf(cc2_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.45/0.68          | (v1_relat_1 @ X3)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ 
% 0.45/0.68             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.45/0.68          | (v1_relat_1 @ 
% 0.45/0.68             (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68              sk_E @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.68  thf(fc6_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('49', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (v1_relat_1 @ 
% 0.45/0.68          (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.45/0.68           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.68  thf('51', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['49', '50'])).
% 0.45/0.68  thf(t148_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ B ) =>
% 0.45/0.68       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i]:
% 0.45/0.68         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.45/0.68          | ~ (v1_relat_1 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.68  thf(t87_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ B ) =>
% 0.45/0.68       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i]:
% 0.45/0.68         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ X13)
% 0.45/0.68          | ~ (v1_relat_1 @ X12))),
% 0.45/0.68      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.45/0.68  thf(t11_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ C ) =>
% 0.45/0.68       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.45/0.68           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.45/0.68          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ X24)
% 0.45/0.68          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.45/0.68          | ~ (v1_relat_1 @ X22))),
% 0.45/0.68      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X1)
% 0.45/0.68          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.68          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.45/0.68          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.45/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.68          | ~ (v1_relat_1 @ X1)
% 0.45/0.68          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.45/0.68          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['52', '55'])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.68          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.45/0.68          | ~ (v1_relat_1 @ X1)
% 0.45/0.68          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))),
% 0.45/0.68      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ X1)
% 0.45/0.68          | ~ (v1_relat_1 @ sk_E)
% 0.45/0.68          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['51', '57'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_E @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('60', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.45/0.68          | (v1_relat_1 @ X3)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('61', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ 
% 0.45/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | (v1_relat_1 @ sk_E))),
% 0.45/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.68      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.68  thf('64', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ X1)
% 0.45/0.68          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.45/0.68      inference('demod', [status(thm)], ['58', '63'])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.45/0.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['40', '64'])).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.45/0.68          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k7_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k7_relat_1 @ sk_E @ X0) @ X1)
% 0.45/0.68           = (k9_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ X1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.68  thf('68', plain,
% 0.45/0.68      (((k9_relat_1 @ sk_E @ sk_F)
% 0.45/0.68         != (k9_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.45/0.68      inference('demod', [status(thm)], ['7', '33', '67'])).
% 0.45/0.68  thf('69', plain,
% 0.45/0.68      ((((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_E))),
% 0.45/0.68      inference('sup-', [status(thm)], ['2', '68'])).
% 0.45/0.68  thf('70', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.68      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.68  thf('71', plain,
% 0.45/0.68      (((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))),
% 0.45/0.68      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.68  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
