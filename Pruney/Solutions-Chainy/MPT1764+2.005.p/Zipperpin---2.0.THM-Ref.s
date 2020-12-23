%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9kc97zPZwq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:04 EST 2020

% Result     : Theorem 7.88s
% Output     : Refutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 184 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          : 1158 (4379 expanded)
%              Number of equality atoms :   33 (  78 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) @ X12 )
        = ( k9_relat_1 @ X14 @ X12 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( ( k3_tmap_1 @ X38 @ X36 @ X39 @ X37 @ X40 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X36 ) @ X40 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X8 @ X9 ) @ ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('65',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['7','33','74'])).

thf('76',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_F )
     != ( k9_relat_1 @ sk_E @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('78',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9kc97zPZwq
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.88/8.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.88/8.14  % Solved by: fo/fo7.sh
% 7.88/8.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.88/8.14  % done 7536 iterations in 7.684s
% 7.88/8.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.88/8.14  % SZS output start Refutation
% 7.88/8.14  thf(sk_C_type, type, sk_C: $i).
% 7.88/8.14  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 7.88/8.14  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.88/8.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.88/8.14  thf(sk_A_type, type, sk_A: $i).
% 7.88/8.14  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 7.88/8.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.88/8.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.88/8.14  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 7.88/8.14  thf(sk_E_type, type, sk_E: $i).
% 7.88/8.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.88/8.14  thf(sk_F_type, type, sk_F: $i).
% 7.88/8.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.88/8.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.88/8.14  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.88/8.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.88/8.14  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.88/8.14  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 7.88/8.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.88/8.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.88/8.14  thf(sk_B_type, type, sk_B: $i).
% 7.88/8.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.88/8.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.88/8.14  thf(sk_D_type, type, sk_D: $i).
% 7.88/8.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.88/8.14  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 7.88/8.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.88/8.14  thf(t75_tmap_1, conjecture,
% 7.88/8.14    (![A:$i]:
% 7.88/8.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.88/8.14       ( ![B:$i]:
% 7.88/8.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 7.88/8.14             ( l1_pre_topc @ B ) ) =>
% 7.88/8.14           ( ![C:$i]:
% 7.88/8.14             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 7.88/8.14               ( ![D:$i]:
% 7.88/8.14                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 7.88/8.14                   ( ![E:$i]:
% 7.88/8.14                     ( ( ( v1_funct_1 @ E ) & 
% 7.88/8.14                         ( v1_funct_2 @
% 7.88/8.14                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 7.88/8.14                         ( m1_subset_1 @
% 7.88/8.14                           E @ 
% 7.88/8.14                           ( k1_zfmisc_1 @
% 7.88/8.14                             ( k2_zfmisc_1 @
% 7.88/8.14                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 7.88/8.14                       ( ( m1_pre_topc @ C @ D ) =>
% 7.88/8.14                         ( ![F:$i]:
% 7.88/8.14                           ( ( m1_subset_1 @
% 7.88/8.14                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 7.88/8.14                             ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 7.88/8.14                               ( ( k7_relset_1 @
% 7.88/8.14                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 7.88/8.14                                   E @ F ) =
% 7.88/8.14                                 ( k7_relset_1 @
% 7.88/8.14                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 7.88/8.14                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.88/8.14  thf(zf_stmt_0, negated_conjecture,
% 7.88/8.14    (~( ![A:$i]:
% 7.88/8.14        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 7.88/8.14            ( l1_pre_topc @ A ) ) =>
% 7.88/8.14          ( ![B:$i]:
% 7.88/8.14            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 7.88/8.14                ( l1_pre_topc @ B ) ) =>
% 7.88/8.14              ( ![C:$i]:
% 7.88/8.14                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 7.88/8.14                  ( ![D:$i]:
% 7.88/8.14                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 7.88/8.14                      ( ![E:$i]:
% 7.88/8.14                        ( ( ( v1_funct_1 @ E ) & 
% 7.88/8.14                            ( v1_funct_2 @
% 7.88/8.14                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 7.88/8.14                            ( m1_subset_1 @
% 7.88/8.14                              E @ 
% 7.88/8.14                              ( k1_zfmisc_1 @
% 7.88/8.14                                ( k2_zfmisc_1 @
% 7.88/8.14                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 7.88/8.14                          ( ( m1_pre_topc @ C @ D ) =>
% 7.88/8.14                            ( ![F:$i]:
% 7.88/8.14                              ( ( m1_subset_1 @
% 7.88/8.14                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 7.88/8.14                                ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 7.88/8.14                                  ( ( k7_relset_1 @
% 7.88/8.14                                      ( u1_struct_0 @ D ) @ 
% 7.88/8.14                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 7.88/8.14                                    ( k7_relset_1 @
% 7.88/8.14                                      ( u1_struct_0 @ C ) @ 
% 7.88/8.14                                      ( u1_struct_0 @ B ) @ 
% 7.88/8.14                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 7.88/8.14    inference('cnf.neg', [status(esa)], [t75_tmap_1])).
% 7.88/8.14  thf('0', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf(t162_relat_1, axiom,
% 7.88/8.14    (![A:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ A ) =>
% 7.88/8.14       ( ![B:$i,C:$i]:
% 7.88/8.14         ( ( r1_tarski @ B @ C ) =>
% 7.88/8.14           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 7.88/8.14             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 7.88/8.14  thf('1', plain,
% 7.88/8.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.88/8.14         (~ (r1_tarski @ X12 @ X13)
% 7.88/8.14          | ((k9_relat_1 @ (k7_relat_1 @ X14 @ X13) @ X12)
% 7.88/8.14              = (k9_relat_1 @ X14 @ X12))
% 7.88/8.14          | ~ (v1_relat_1 @ X14))),
% 7.88/8.14      inference('cnf', [status(esa)], [t162_relat_1])).
% 7.88/8.14  thf('2', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X0)
% 7.88/8.14          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 7.88/8.14              = (k9_relat_1 @ X0 @ sk_F)))),
% 7.88/8.14      inference('sup-', [status(thm)], ['0', '1'])).
% 7.88/8.14  thf('3', plain,
% 7.88/8.14      (((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 7.88/8.14         sk_F)
% 7.88/8.14         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 7.88/8.14             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('4', plain,
% 7.88/8.14      ((m1_subset_1 @ sk_E @ 
% 7.88/8.14        (k1_zfmisc_1 @ 
% 7.88/8.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf(redefinition_k7_relset_1, axiom,
% 7.88/8.14    (![A:$i,B:$i,C:$i,D:$i]:
% 7.88/8.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.88/8.14       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 7.88/8.14  thf('5', plain,
% 7.88/8.14      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 7.88/8.14         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 7.88/8.14          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 7.88/8.14      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 7.88/8.14  thf('6', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 7.88/8.14           X0) = (k9_relat_1 @ sk_E @ X0))),
% 7.88/8.14      inference('sup-', [status(thm)], ['4', '5'])).
% 7.88/8.14  thf('7', plain,
% 7.88/8.14      (((k9_relat_1 @ sk_E @ sk_F)
% 7.88/8.14         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 7.88/8.14             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 7.88/8.14      inference('demod', [status(thm)], ['3', '6'])).
% 7.88/8.14  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('10', plain,
% 7.88/8.14      ((m1_subset_1 @ sk_E @ 
% 7.88/8.14        (k1_zfmisc_1 @ 
% 7.88/8.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf(d5_tmap_1, axiom,
% 7.88/8.14    (![A:$i]:
% 7.88/8.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.88/8.14       ( ![B:$i]:
% 7.88/8.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 7.88/8.14             ( l1_pre_topc @ B ) ) =>
% 7.88/8.14           ( ![C:$i]:
% 7.88/8.14             ( ( m1_pre_topc @ C @ A ) =>
% 7.88/8.14               ( ![D:$i]:
% 7.88/8.14                 ( ( m1_pre_topc @ D @ A ) =>
% 7.88/8.14                   ( ![E:$i]:
% 7.88/8.14                     ( ( ( v1_funct_1 @ E ) & 
% 7.88/8.14                         ( v1_funct_2 @
% 7.88/8.14                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 7.88/8.14                         ( m1_subset_1 @
% 7.88/8.14                           E @ 
% 7.88/8.14                           ( k1_zfmisc_1 @
% 7.88/8.14                             ( k2_zfmisc_1 @
% 7.88/8.14                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 7.88/8.14                       ( ( m1_pre_topc @ D @ C ) =>
% 7.88/8.14                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 7.88/8.14                           ( k2_partfun1 @
% 7.88/8.14                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 7.88/8.14                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.88/8.14  thf('11', plain,
% 7.88/8.14      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.88/8.14         ((v2_struct_0 @ X36)
% 7.88/8.14          | ~ (v2_pre_topc @ X36)
% 7.88/8.14          | ~ (l1_pre_topc @ X36)
% 7.88/8.14          | ~ (m1_pre_topc @ X37 @ X38)
% 7.88/8.14          | ~ (m1_pre_topc @ X37 @ X39)
% 7.88/8.14          | ((k3_tmap_1 @ X38 @ X36 @ X39 @ X37 @ X40)
% 7.88/8.14              = (k2_partfun1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X36) @ 
% 7.88/8.14                 X40 @ (u1_struct_0 @ X37)))
% 7.88/8.14          | ~ (m1_subset_1 @ X40 @ 
% 7.88/8.14               (k1_zfmisc_1 @ 
% 7.88/8.14                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X36))))
% 7.88/8.14          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X36))
% 7.88/8.14          | ~ (v1_funct_1 @ X40)
% 7.88/8.14          | ~ (m1_pre_topc @ X39 @ X38)
% 7.88/8.14          | ~ (l1_pre_topc @ X38)
% 7.88/8.14          | ~ (v2_pre_topc @ X38)
% 7.88/8.14          | (v2_struct_0 @ X38))),
% 7.88/8.14      inference('cnf', [status(esa)], [d5_tmap_1])).
% 7.88/8.14  thf('12', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         ((v2_struct_0 @ X0)
% 7.88/8.14          | ~ (v2_pre_topc @ X0)
% 7.88/8.14          | ~ (l1_pre_topc @ X0)
% 7.88/8.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 7.88/8.14          | ~ (v1_funct_1 @ sk_E)
% 7.88/8.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 7.88/8.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 7.88/8.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 7.88/8.14                 sk_E @ (u1_struct_0 @ X1)))
% 7.88/8.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 7.88/8.14          | ~ (m1_pre_topc @ X1 @ X0)
% 7.88/8.14          | ~ (l1_pre_topc @ sk_B)
% 7.88/8.14          | ~ (v2_pre_topc @ sk_B)
% 7.88/8.14          | (v2_struct_0 @ sk_B))),
% 7.88/8.14      inference('sup-', [status(thm)], ['10', '11'])).
% 7.88/8.14  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('14', plain,
% 7.88/8.14      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('15', plain,
% 7.88/8.14      ((m1_subset_1 @ sk_E @ 
% 7.88/8.14        (k1_zfmisc_1 @ 
% 7.88/8.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf(redefinition_k2_partfun1, axiom,
% 7.88/8.14    (![A:$i,B:$i,C:$i,D:$i]:
% 7.88/8.14     ( ( ( v1_funct_1 @ C ) & 
% 7.88/8.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.88/8.14       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 7.88/8.14  thf('16', plain,
% 7.88/8.14      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 7.88/8.14         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 7.88/8.14          | ~ (v1_funct_1 @ X32)
% 7.88/8.14          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 7.88/8.14      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 7.88/8.14  thf('17', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 7.88/8.14            X0) = (k7_relat_1 @ sk_E @ X0))
% 7.88/8.14          | ~ (v1_funct_1 @ sk_E))),
% 7.88/8.14      inference('sup-', [status(thm)], ['15', '16'])).
% 7.88/8.14  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('19', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 7.88/8.14           X0) = (k7_relat_1 @ sk_E @ X0))),
% 7.88/8.14      inference('demod', [status(thm)], ['17', '18'])).
% 7.88/8.14  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('22', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         ((v2_struct_0 @ X0)
% 7.88/8.14          | ~ (v2_pre_topc @ X0)
% 7.88/8.14          | ~ (l1_pre_topc @ X0)
% 7.88/8.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 7.88/8.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 7.88/8.14              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 7.88/8.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 7.88/8.14          | ~ (m1_pre_topc @ X1 @ X0)
% 7.88/8.14          | (v2_struct_0 @ sk_B))),
% 7.88/8.14      inference('demod', [status(thm)], ['12', '13', '14', '19', '20', '21'])).
% 7.88/8.14  thf('23', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((v2_struct_0 @ sk_B)
% 7.88/8.14          | ~ (m1_pre_topc @ X0 @ sk_A)
% 7.88/8.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 7.88/8.14          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 7.88/8.14              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 7.88/8.14          | ~ (l1_pre_topc @ sk_A)
% 7.88/8.14          | ~ (v2_pre_topc @ sk_A)
% 7.88/8.14          | (v2_struct_0 @ sk_A))),
% 7.88/8.14      inference('sup-', [status(thm)], ['9', '22'])).
% 7.88/8.14  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('26', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((v2_struct_0 @ sk_B)
% 7.88/8.14          | ~ (m1_pre_topc @ X0 @ sk_A)
% 7.88/8.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 7.88/8.14          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 7.88/8.14              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 7.88/8.14          | (v2_struct_0 @ sk_A))),
% 7.88/8.14      inference('demod', [status(thm)], ['23', '24', '25'])).
% 7.88/8.14  thf('27', plain,
% 7.88/8.14      (((v2_struct_0 @ sk_A)
% 7.88/8.14        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 7.88/8.14            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 7.88/8.14        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 7.88/8.14        | (v2_struct_0 @ sk_B))),
% 7.88/8.14      inference('sup-', [status(thm)], ['8', '26'])).
% 7.88/8.14  thf('28', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('29', plain,
% 7.88/8.14      (((v2_struct_0 @ sk_A)
% 7.88/8.14        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 7.88/8.14            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 7.88/8.14        | (v2_struct_0 @ sk_B))),
% 7.88/8.14      inference('demod', [status(thm)], ['27', '28'])).
% 7.88/8.14  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('31', plain,
% 7.88/8.14      (((v2_struct_0 @ sk_B)
% 7.88/8.14        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 7.88/8.14            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 7.88/8.14      inference('clc', [status(thm)], ['29', '30'])).
% 7.88/8.14  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf('33', plain,
% 7.88/8.14      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 7.88/8.14         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 7.88/8.14      inference('clc', [status(thm)], ['31', '32'])).
% 7.88/8.14  thf(dt_k7_relat_1, axiom,
% 7.88/8.14    (![A:$i,B:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 7.88/8.14  thf('34', plain,
% 7.88/8.14      (![X5 : $i, X6 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 7.88/8.14      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.88/8.14  thf('35', plain,
% 7.88/8.14      ((m1_subset_1 @ sk_E @ 
% 7.88/8.14        (k1_zfmisc_1 @ 
% 7.88/8.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf(cc2_relset_1, axiom,
% 7.88/8.14    (![A:$i,B:$i,C:$i]:
% 7.88/8.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.88/8.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.88/8.14  thf('36', plain,
% 7.88/8.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.88/8.14         ((v5_relat_1 @ X22 @ X24)
% 7.88/8.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 7.88/8.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.88/8.14  thf('37', plain, ((v5_relat_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 7.88/8.14      inference('sup-', [status(thm)], ['35', '36'])).
% 7.88/8.14  thf(d19_relat_1, axiom,
% 7.88/8.14    (![A:$i,B:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ B ) =>
% 7.88/8.14       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 7.88/8.14  thf('38', plain,
% 7.88/8.14      (![X3 : $i, X4 : $i]:
% 7.88/8.14         (~ (v5_relat_1 @ X3 @ X4)
% 7.88/8.14          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 7.88/8.14          | ~ (v1_relat_1 @ X3))),
% 7.88/8.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.88/8.14  thf('39', plain,
% 7.88/8.14      ((~ (v1_relat_1 @ sk_E)
% 7.88/8.14        | (r1_tarski @ (k2_relat_1 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 7.88/8.14      inference('sup-', [status(thm)], ['37', '38'])).
% 7.88/8.14  thf('40', plain,
% 7.88/8.14      ((m1_subset_1 @ sk_E @ 
% 7.88/8.14        (k1_zfmisc_1 @ 
% 7.88/8.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 7.88/8.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.14  thf(cc1_relset_1, axiom,
% 7.88/8.14    (![A:$i,B:$i,C:$i]:
% 7.88/8.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.88/8.14       ( v1_relat_1 @ C ) ))).
% 7.88/8.14  thf('41', plain,
% 7.88/8.14      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.88/8.14         ((v1_relat_1 @ X19)
% 7.88/8.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 7.88/8.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.88/8.14  thf('42', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.14      inference('sup-', [status(thm)], ['40', '41'])).
% 7.88/8.14  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 7.88/8.14      inference('demod', [status(thm)], ['39', '42'])).
% 7.88/8.14  thf(t146_relat_1, axiom,
% 7.88/8.14    (![A:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ A ) =>
% 7.88/8.14       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 7.88/8.14  thf('44', plain,
% 7.88/8.14      (![X7 : $i]:
% 7.88/8.14         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 7.88/8.14          | ~ (v1_relat_1 @ X7))),
% 7.88/8.14      inference('cnf', [status(esa)], [t146_relat_1])).
% 7.88/8.14  thf(t147_relat_1, axiom,
% 7.88/8.14    (![A:$i,B:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ B ) =>
% 7.88/8.14       ( r1_tarski @
% 7.88/8.14         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 7.88/8.14  thf('45', plain,
% 7.88/8.14      (![X8 : $i, X9 : $i]:
% 7.88/8.14         ((r1_tarski @ (k9_relat_1 @ X8 @ X9) @ 
% 7.88/8.14           (k9_relat_1 @ X8 @ (k1_relat_1 @ X8)))
% 7.88/8.14          | ~ (v1_relat_1 @ X8))),
% 7.88/8.14      inference('cnf', [status(esa)], [t147_relat_1])).
% 7.88/8.14  thf('46', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 7.88/8.14          | ~ (v1_relat_1 @ X0)
% 7.88/8.14          | ~ (v1_relat_1 @ X0))),
% 7.88/8.14      inference('sup+', [status(thm)], ['44', '45'])).
% 7.88/8.14  thf('47', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X0)
% 7.88/8.14          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 7.88/8.14      inference('simplify', [status(thm)], ['46'])).
% 7.88/8.14  thf(t148_relat_1, axiom,
% 7.88/8.14    (![A:$i,B:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ B ) =>
% 7.88/8.14       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 7.88/8.14  thf('48', plain,
% 7.88/8.14      (![X10 : $i, X11 : $i]:
% 7.88/8.14         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 7.88/8.14          | ~ (v1_relat_1 @ X10))),
% 7.88/8.14      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.88/8.14  thf('49', plain,
% 7.88/8.14      (![X3 : $i, X4 : $i]:
% 7.88/8.14         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 7.88/8.14          | (v5_relat_1 @ X3 @ X4)
% 7.88/8.14          | ~ (v1_relat_1 @ X3))),
% 7.88/8.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.88/8.14  thf('50', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.14         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 7.88/8.14          | ~ (v1_relat_1 @ X1)
% 7.88/8.14          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 7.88/8.14          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 7.88/8.14      inference('sup-', [status(thm)], ['48', '49'])).
% 7.88/8.14  thf('51', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X0)
% 7.88/8.14          | (v5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 7.88/8.14          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.88/8.14          | ~ (v1_relat_1 @ X0))),
% 7.88/8.14      inference('sup-', [status(thm)], ['47', '50'])).
% 7.88/8.14  thf('52', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.88/8.14          | (v5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 7.88/8.14          | ~ (v1_relat_1 @ X0))),
% 7.88/8.14      inference('simplify', [status(thm)], ['51'])).
% 7.88/8.14  thf('53', plain,
% 7.88/8.14      (![X5 : $i, X6 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 7.88/8.14      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.88/8.14  thf('54', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X0)
% 7.88/8.14          | (v5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 7.88/8.14      inference('clc', [status(thm)], ['52', '53'])).
% 7.88/8.14  thf('55', plain,
% 7.88/8.14      (![X3 : $i, X4 : $i]:
% 7.88/8.14         (~ (v5_relat_1 @ X3 @ X4)
% 7.88/8.14          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 7.88/8.14          | ~ (v1_relat_1 @ X3))),
% 7.88/8.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.88/8.14  thf('56', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X0)
% 7.88/8.14          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.88/8.14          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 7.88/8.14             (k2_relat_1 @ X0)))),
% 7.88/8.14      inference('sup-', [status(thm)], ['54', '55'])).
% 7.88/8.14  thf('57', plain,
% 7.88/8.14      (![X5 : $i, X6 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 7.88/8.14      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.88/8.14  thf('58', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 7.88/8.14           (k2_relat_1 @ X0))
% 7.88/8.14          | ~ (v1_relat_1 @ X0))),
% 7.88/8.14      inference('clc', [status(thm)], ['56', '57'])).
% 7.88/8.14  thf(t1_xboole_1, axiom,
% 7.88/8.14    (![A:$i,B:$i,C:$i]:
% 7.88/8.14     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 7.88/8.14       ( r1_tarski @ A @ C ) ))).
% 7.88/8.14  thf('59', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.14         (~ (r1_tarski @ X0 @ X1)
% 7.88/8.14          | ~ (r1_tarski @ X1 @ X2)
% 7.88/8.14          | (r1_tarski @ X0 @ X2))),
% 7.88/8.14      inference('cnf', [status(esa)], [t1_xboole_1])).
% 7.88/8.14  thf('60', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X0)
% 7.88/8.14          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 7.88/8.14          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 7.88/8.14      inference('sup-', [status(thm)], ['58', '59'])).
% 7.88/8.14  thf('61', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 7.88/8.14           (u1_struct_0 @ sk_B))
% 7.88/8.14          | ~ (v1_relat_1 @ sk_E))),
% 7.88/8.14      inference('sup-', [status(thm)], ['43', '60'])).
% 7.88/8.14  thf('62', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.14      inference('sup-', [status(thm)], ['40', '41'])).
% 7.88/8.14  thf('63', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ 
% 7.88/8.14          (u1_struct_0 @ sk_B))),
% 7.88/8.14      inference('demod', [status(thm)], ['61', '62'])).
% 7.88/8.14  thf(t87_relat_1, axiom,
% 7.88/8.14    (![A:$i,B:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ B ) =>
% 7.88/8.14       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 7.88/8.14  thf('64', plain,
% 7.88/8.14      (![X17 : $i, X18 : $i]:
% 7.88/8.14         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)) @ X18)
% 7.88/8.14          | ~ (v1_relat_1 @ X17))),
% 7.88/8.14      inference('cnf', [status(esa)], [t87_relat_1])).
% 7.88/8.14  thf(t11_relset_1, axiom,
% 7.88/8.14    (![A:$i,B:$i,C:$i]:
% 7.88/8.14     ( ( v1_relat_1 @ C ) =>
% 7.88/8.14       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 7.88/8.14           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 7.88/8.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 7.88/8.14  thf('65', plain,
% 7.88/8.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 7.88/8.14         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 7.88/8.14          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 7.88/8.14          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 7.88/8.14          | ~ (v1_relat_1 @ X29))),
% 7.88/8.14      inference('cnf', [status(esa)], [t11_relset_1])).
% 7.88/8.14  thf('66', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ X1)
% 7.88/8.14          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 7.88/8.14          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 7.88/8.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 7.88/8.14          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 7.88/8.14      inference('sup-', [status(thm)], ['64', '65'])).
% 7.88/8.14  thf('67', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 7.88/8.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 7.88/8.14          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 7.88/8.14          | ~ (v1_relat_1 @ sk_E))),
% 7.88/8.14      inference('sup-', [status(thm)], ['63', '66'])).
% 7.88/8.14  thf('68', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.14      inference('sup-', [status(thm)], ['40', '41'])).
% 7.88/8.14  thf('69', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 7.88/8.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 7.88/8.14          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 7.88/8.14      inference('demod', [status(thm)], ['67', '68'])).
% 7.88/8.14  thf('70', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         (~ (v1_relat_1 @ sk_E)
% 7.88/8.14          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 7.88/8.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B)))))),
% 7.88/8.14      inference('sup-', [status(thm)], ['34', '69'])).
% 7.88/8.14  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.14      inference('sup-', [status(thm)], ['40', '41'])).
% 7.88/8.14  thf('72', plain,
% 7.88/8.14      (![X0 : $i]:
% 7.88/8.14         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 7.88/8.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 7.88/8.14      inference('demod', [status(thm)], ['70', '71'])).
% 7.88/8.14  thf('73', plain,
% 7.88/8.14      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 7.88/8.14         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 7.88/8.14          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 7.88/8.14      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 7.88/8.14  thf('74', plain,
% 7.88/8.14      (![X0 : $i, X1 : $i]:
% 7.88/8.14         ((k7_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 7.88/8.14           (k7_relat_1 @ sk_E @ X0) @ X1)
% 7.88/8.14           = (k9_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ X1))),
% 7.88/8.14      inference('sup-', [status(thm)], ['72', '73'])).
% 7.88/8.14  thf('75', plain,
% 7.88/8.14      (((k9_relat_1 @ sk_E @ sk_F)
% 7.88/8.14         != (k9_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 7.88/8.14      inference('demod', [status(thm)], ['7', '33', '74'])).
% 7.88/8.14  thf('76', plain,
% 7.88/8.14      ((((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))
% 7.88/8.14        | ~ (v1_relat_1 @ sk_E))),
% 7.88/8.14      inference('sup-', [status(thm)], ['2', '75'])).
% 7.88/8.14  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.14      inference('sup-', [status(thm)], ['40', '41'])).
% 7.88/8.14  thf('78', plain,
% 7.88/8.14      (((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))),
% 7.88/8.14      inference('demod', [status(thm)], ['76', '77'])).
% 7.88/8.14  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 7.88/8.14  
% 7.88/8.14  % SZS output end Refutation
% 7.88/8.14  
% 8.00/8.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
