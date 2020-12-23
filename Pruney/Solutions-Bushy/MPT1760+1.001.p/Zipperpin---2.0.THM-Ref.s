%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1760+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CyVtzcQzpv

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:12 EST 2020

% Result     : Theorem 8.64s
% Output     : Refutation 8.64s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 646 expanded)
%              Number of leaves         :   31 ( 192 expanded)
%              Depth                    :   28
%              Number of atoms          : 3270 (49636 expanded)
%              Number of equality atoms :   12 (  66 expanded)
%              Maximal formula depth    :   30 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t71_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                        & ( v5_pre_topc @ E @ B @ C )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ F @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ F @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ F @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ F @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ C ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ D @ C )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                          & ( v5_pre_topc @ E @ B @ C )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ F @ D ) )
                                & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ F @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ F @ D ) @ D @ B )
                                & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ F @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) )
                                & ( v1_funct_2 @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ C ) )
                                & ( v5_pre_topc @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ D @ C )
                                & ( m1_subset_1 @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_F @ sk_D ) @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_tmap_1,axiom,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( v5_pre_topc @ E @ B @ C )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ F @ D ) @ D @ B ) )
                           => ( v5_pre_topc @ ( k2_tmap_1 @ A @ C @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ F @ E ) @ D ) @ D @ C ) ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X27 @ X29 @ ( k1_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X29 ) @ X28 @ X30 ) @ X26 ) @ X26 @ X29 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X27 @ X25 @ X28 @ X26 ) @ X26 @ X25 )
      | ~ ( v5_pre_topc @ X30 @ X25 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_F @ X2 ) @ X2 @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ sk_F @ X1 ) @ X2 ) @ X2 @ X0 )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_F @ X2 ) @ X2 @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ sk_F @ X1 ) @ X2 ) @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ X0 ) @ X0 @ sk_C )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_F @ X0 ) @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_E @ sk_B @ sk_C )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_F @ X0 )
        = ( k5_relat_1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_F @ X0 )
        = ( k5_relat_1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
      = ( k5_relat_1 @ sk_F @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v5_pre_topc @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ X0 @ sk_C )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_F @ X0 ) @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','22','23','24','25','26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ B @ C )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k5_relat_1 @ D @ E ) )
        & ( v1_funct_2 @ ( k5_relat_1 @ D @ E ) @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X18 ) ) )
      | ( v1_funct_2 @ ( k5_relat_1 @ X14 @ X17 ) @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ X1 ) @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ X1 ) @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X1 @ X2 @ X4 @ X5 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X0 @ sk_F @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X0 @ sk_F @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('61',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

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

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X7 @ X8 @ X6 @ X9 ) @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_F @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X1 @ X2 @ X4 @ X5 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('74',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','92'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('94',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('104',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('106',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('107',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X7 @ X8 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_F @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference(split,[status(esa)],['32'])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['101','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('133',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('134',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('135',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('137',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('138',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X7 @ X8 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_F @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E )
    = ( k5_relat_1 @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('150',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('151',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['133','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['132','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('164',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['100','131','162','163'])).

thf('165',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_F @ sk_E ) @ sk_D ) @ sk_D @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['35','164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['0','172'])).


%------------------------------------------------------------------------------
