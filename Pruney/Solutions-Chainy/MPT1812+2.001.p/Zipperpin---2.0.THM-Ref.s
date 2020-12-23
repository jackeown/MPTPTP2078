%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TLIIN4DDVd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  326 ( 896 expanded)
%              Number of leaves         :   23 ( 258 expanded)
%              Depth                    :   21
%              Number of atoms          : 7677 (91875 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   30 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t128_tmap_1,conjecture,(
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
                & ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                      <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                          & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v1_tsep_1 @ C @ A )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_tsep_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_tmap_1])).

thf('0',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t126_tmap_1,axiom,(
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
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23','24','25','26'])).

thf('28',plain,(
    v1_tsep_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_tsep_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_tsep_1 @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r4_tsep_1 @ X6 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( v1_tsep_1 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t88_tsep_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','41'])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_E )
   <= ~ ( v1_funct_1 @ sk_E ) ),
    inference(split,[status(esa)],['43'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('59',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72','73','74','75'])).

thf('77',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','78'])).

thf('80',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100','101','102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf('105',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126','127','128','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['117','130'])).

thf('132',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153','154','155','156'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['144','157'])).

thf('159',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['43'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('172',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177','178','179','180','181','182','183'])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['171','184'])).

thf('186',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['43'])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('199',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','201'])).

thf('203',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['202','203','204','205','206','207','208','209','210'])).

thf('212',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['198','211'])).

thf('213',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('214',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['43'])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('226',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('227',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','229'])).

thf('231',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['230','231','232','233','234','235','236','237','238'])).

thf('240',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['226','239'])).

thf('241',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['225','240'])).

thf('242',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['43'])).

thf('243',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,
    ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('253',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['253'])).

thf('255',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
   <= ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['255'])).

thf('257',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['257'])).

thf('259',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['259'])).

thf('261',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
   <= ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['261'])).

thf('263',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['263'])).

thf('265',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['265'])).

thf('267',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['267'])).

thf('269',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('277',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['272','273','274','275','276','277','278','279','280','281','282'])).

thf('284',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['268','283'])).

thf('285',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['266','284'])).

thf('286',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['264','285'])).

thf('287',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['262','286'])).

thf('288',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['260','287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['258','288'])).

thf('290',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['256','289'])).

thf('291',plain,
    ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['43'])).

thf('292',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('297',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      & ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['296','297'])).

thf('299',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','13','53','56','59','62','89','116','143','170','197','224','251','252','254','300'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TLIIN4DDVd
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 212 iterations in 0.108s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.20/0.59  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.59  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.20/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.59  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.59  thf(t128_tmap_1, conjecture,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59             ( l1_pre_topc @ B ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 0.20/0.59                 ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.59               ( ![D:$i]:
% 0.20/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.20/0.59                     ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.59                   ( ![E:$i]:
% 0.20/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                         ( v1_funct_2 @
% 0.20/0.59                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                           ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                         ( m1_subset_1 @
% 0.20/0.59                           E @ 
% 0.20/0.59                           ( k1_zfmisc_1 @
% 0.20/0.59                             ( k2_zfmisc_1 @
% 0.20/0.59                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.59                       ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                           ( v1_funct_2 @
% 0.20/0.59                             E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                             ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                           ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.20/0.59                           ( m1_subset_1 @
% 0.20/0.59                             E @ 
% 0.20/0.59                             ( k1_zfmisc_1 @
% 0.20/0.59                               ( k2_zfmisc_1 @
% 0.20/0.59                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                                 ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.20/0.59                         ( ( v1_funct_1 @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) ) & 
% 0.20/0.59                           ( v1_funct_2 @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                           ( v5_pre_topc @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                             C @ B ) & 
% 0.20/0.59                           ( m1_subset_1 @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                             ( k1_zfmisc_1 @
% 0.20/0.59                               ( k2_zfmisc_1 @
% 0.20/0.59                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.20/0.59                           ( v1_funct_1 @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) & 
% 0.20/0.59                           ( v1_funct_2 @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                           ( v5_pre_topc @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                             D @ B ) & 
% 0.20/0.59                           ( m1_subset_1 @
% 0.20/0.59                             ( k3_tmap_1 @
% 0.20/0.59                               A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                             ( k1_zfmisc_1 @
% 0.20/0.59                               ( k2_zfmisc_1 @
% 0.20/0.59                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]:
% 0.20/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.59            ( l1_pre_topc @ A ) ) =>
% 0.20/0.59          ( ![B:$i]:
% 0.20/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59                ( l1_pre_topc @ B ) ) =>
% 0.20/0.59              ( ![C:$i]:
% 0.20/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 0.20/0.59                    ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.59                  ( ![D:$i]:
% 0.20/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.20/0.59                        ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.59                      ( ![E:$i]:
% 0.20/0.59                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                            ( v1_funct_2 @
% 0.20/0.59                              E @ 
% 0.20/0.59                              ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                              ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                            ( m1_subset_1 @
% 0.20/0.59                              E @ 
% 0.20/0.59                              ( k1_zfmisc_1 @
% 0.20/0.59                                ( k2_zfmisc_1 @
% 0.20/0.59                                  ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                                  ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.59                          ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                              ( v1_funct_2 @
% 0.20/0.59                                E @ 
% 0.20/0.59                                ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                                ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                              ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.20/0.59                              ( m1_subset_1 @
% 0.20/0.59                                E @ 
% 0.20/0.59                                ( k1_zfmisc_1 @
% 0.20/0.59                                  ( k2_zfmisc_1 @
% 0.20/0.59                                    ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                                    ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.20/0.59                            ( ( v1_funct_1 @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) ) & 
% 0.20/0.59                              ( v1_funct_2 @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                              ( v5_pre_topc @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                                C @ B ) & 
% 0.20/0.59                              ( m1_subset_1 @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                                ( k1_zfmisc_1 @
% 0.20/0.59                                  ( k2_zfmisc_1 @
% 0.20/0.59                                    ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.20/0.59                              ( v1_funct_1 @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) & 
% 0.20/0.59                              ( v1_funct_2 @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                                ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                              ( v5_pre_topc @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                                D @ B ) & 
% 0.20/0.59                              ( m1_subset_1 @
% 0.20/0.59                                ( k3_tmap_1 @
% 0.20/0.59                                  A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                                ( k1_zfmisc_1 @
% 0.20/0.59                                  ( k2_zfmisc_1 @
% 0.20/0.59                                    ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t128_tmap_1])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E))
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E))) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['2'])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_C @ sk_B)
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_C @ sk_B)) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['4'])).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['6'])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E))
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E))) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['8'])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['10'])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t126_tmap_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59             ( l1_pre_topc @ B ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.59               ( ![D:$i]:
% 0.20/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.59                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.20/0.59                     ( ![E:$i]:
% 0.20/0.59                       ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                           ( v1_funct_2 @
% 0.20/0.59                             E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                             ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                           ( m1_subset_1 @
% 0.20/0.59                             E @ 
% 0.20/0.59                             ( k1_zfmisc_1 @
% 0.20/0.59                               ( k2_zfmisc_1 @
% 0.20/0.59                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                                 ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.59                         ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                             ( v1_funct_2 @
% 0.20/0.59                               E @ 
% 0.20/0.59                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                               ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                             ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.20/0.59                             ( m1_subset_1 @
% 0.20/0.59                               E @ 
% 0.20/0.59                               ( k1_zfmisc_1 @
% 0.20/0.59                                 ( k2_zfmisc_1 @
% 0.20/0.59                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.59                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.20/0.59                           ( ( v1_funct_1 @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) ) & 
% 0.20/0.59                             ( v1_funct_2 @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                             ( v5_pre_topc @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                               C @ B ) & 
% 0.20/0.59                             ( m1_subset_1 @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.59                               ( k1_zfmisc_1 @
% 0.20/0.59                                 ( k2_zfmisc_1 @
% 0.20/0.59                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.20/0.59                             ( v1_funct_1 @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) & 
% 0.20/0.59                             ( v1_funct_2 @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                             ( v5_pre_topc @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                               D @ B ) & 
% 0.20/0.59                             ( m1_subset_1 @
% 0.20/0.59                               ( k3_tmap_1 @
% 0.20/0.59                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.59                               ( k1_zfmisc_1 @
% 0.20/0.59                                 ( k2_zfmisc_1 @
% 0.20/0.59                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (m1_subset_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59             (k1_zfmisc_1 @ 
% 0.20/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (m1_subset_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59             (k1_zfmisc_1 @ 
% 0.20/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.59  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['18', '19', '20', '21', '22', '23', '24', '25', '26'])).
% 0.20/0.59  thf('28', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('29', plain, ((v1_tsep_1 @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t88_tsep_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.59               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.59         (~ (v1_tsep_1 @ X5 @ X6)
% 0.20/0.59          | ~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.59          | (r4_tsep_1 @ X6 @ X5 @ X7)
% 0.20/0.59          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.59          | ~ (v1_tsep_1 @ X7 @ X6)
% 0.20/0.59          | ~ (l1_pre_topc @ X6)
% 0.20/0.59          | ~ (v2_pre_topc @ X6)
% 0.20/0.59          | (v2_struct_0 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t88_tsep_1])).
% 0.20/0.59  thf('31', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_A)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.59          | (r4_tsep_1 @ sk_A @ sk_C @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.59  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_A)
% 0.20/0.59          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.59          | (r4_tsep_1 @ sk_A @ sk_C @ X0))),
% 0.20/0.59      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (((r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['28', '35'])).
% 0.20/0.59  thf('37', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('38', plain, (((r4_tsep_1 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.59  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('40', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '40'])).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (m1_subset_1 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E) @ 
% 0.20/0.59            (k1_zfmisc_1 @ 
% 0.20/0.59             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['14', '41'])).
% 0.20/0.59  thf('43', plain,
% 0.20/0.59      ((~ (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (v5_pre_topc @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_D @ sk_E) @ 
% 0.20/0.59             sk_D @ sk_B)
% 0.20/0.59        | ~ (v1_funct_2 @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_D @ sk_E) @ 
% 0.20/0.59             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v1_funct_1 @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_D @ sk_E))
% 0.20/0.59        | ~ (m1_subset_1 @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_C @ sk_E) @ 
% 0.20/0.59             (k1_zfmisc_1 @ 
% 0.20/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (v5_pre_topc @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_C @ sk_E) @ 
% 0.20/0.59             sk_C @ sk_B)
% 0.20/0.59        | ~ (v1_funct_2 @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_C @ sk_E) @ 
% 0.20/0.59             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v1_funct_1 @ 
% 0.20/0.59             (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59              sk_C @ sk_E))
% 0.20/0.59        | ~ (m1_subset_1 @ sk_E @ 
% 0.20/0.59             (k1_zfmisc_1 @ 
% 0.20/0.59              (k2_zfmisc_1 @ 
% 0.20/0.59               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59               (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      ((~ (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['42', '44'])).
% 0.20/0.59  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.59  thf('48', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.59  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.59  thf('52', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.59  thf('54', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('55', plain, ((~ (v1_funct_1 @ sk_E)) <= (~ ((v1_funct_1 @ sk_E)))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('56', plain, (((v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      ((~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59           (u1_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ sk_E @ 
% 0.20/0.59               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59               (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (((v1_funct_2 @ sk_E @ 
% 0.20/0.59         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59         (u1_struct_0 @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('61', plain,
% 0.20/0.59      ((~ (m1_subset_1 @ sk_E @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B)))))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ sk_E @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ 
% 0.20/0.59                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59                 (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      (((m1_subset_1 @ sk_E @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59           (u1_struct_0 @ sk_B)))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.59  thf('63', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('64', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('65', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (m1_subset_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59             (k1_zfmisc_1 @ 
% 0.20/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (m1_subset_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59             (k1_zfmisc_1 @ 
% 0.20/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.59  thf('67', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['64', '66'])).
% 0.20/0.59  thf('68', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('71', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('72', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('76', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['67', '68', '69', '70', '71', '72', '73', '74', '75'])).
% 0.20/0.59  thf('77', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('78', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.59  thf('79', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (m1_subset_1 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E) @ 
% 0.20/0.59            (k1_zfmisc_1 @ 
% 0.20/0.59             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['63', '78'])).
% 0.20/0.59  thf('80', plain,
% 0.20/0.59      ((~ (m1_subset_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (k1_zfmisc_1 @ 
% 0.20/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('81', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.59  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('83', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.59  thf('84', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('85', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.59  thf('86', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('87', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.59  thf('88', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('89', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.59  thf('90', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('91', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('92', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (v1_funct_2 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('93', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (v1_funct_2 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['92'])).
% 0.20/0.59  thf('94', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_2 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['91', '93'])).
% 0.20/0.59  thf('95', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('99', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('103', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_2 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['94', '95', '96', '97', '98', '99', '100', '101', '102'])).
% 0.20/0.59  thf('104', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | (v1_funct_2 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E) @ 
% 0.20/0.59            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['90', '103'])).
% 0.20/0.59  thf('105', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('106', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v1_funct_2 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E) @ 
% 0.20/0.59            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.59  thf('107', plain,
% 0.20/0.59      ((~ (v1_funct_2 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('108', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.59  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('110', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.59  thf('111', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('112', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['110', '111'])).
% 0.20/0.59  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('114', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['112', '113'])).
% 0.20/0.59  thf('115', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('116', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.59  thf('117', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('118', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('119', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (v1_funct_2 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59             (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('120', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (v1_funct_2 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59             (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['119'])).
% 0.20/0.59  thf('121', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_2 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['118', '120'])).
% 0.20/0.59  thf('122', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('124', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('126', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('127', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('130', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_2 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['121', '122', '123', '124', '125', '126', '127', '128', '129'])).
% 0.20/0.59  thf('131', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | (v1_funct_2 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E) @ 
% 0.20/0.59            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['117', '130'])).
% 0.20/0.59  thf('132', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('133', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v1_funct_2 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E) @ 
% 0.20/0.59            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['131', '132'])).
% 0.20/0.59  thf('134', plain,
% 0.20/0.59      ((~ (v1_funct_2 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('135', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['133', '134'])).
% 0.20/0.59  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('137', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['135', '136'])).
% 0.20/0.59  thf('138', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('139', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['137', '138'])).
% 0.20/0.59  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('141', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['139', '140'])).
% 0.20/0.59  thf('142', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('143', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['141', '142'])).
% 0.20/0.59  thf('144', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('145', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('146', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (v5_pre_topc @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59             X1 @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('147', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (v5_pre_topc @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59             X1 @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['146'])).
% 0.20/0.59  thf('148', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v5_pre_topc @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           sk_D @ sk_B)
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['145', '147'])).
% 0.20/0.59  thf('149', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('150', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('151', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('152', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('153', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('154', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('157', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v5_pre_topc @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           sk_D @ sk_B)
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['148', '149', '150', '151', '152', '153', '154', '155', '156'])).
% 0.20/0.59  thf('158', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | (v5_pre_topc @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E) @ 
% 0.20/0.59            sk_D @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['144', '157'])).
% 0.20/0.59  thf('159', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('160', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v5_pre_topc @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E) @ 
% 0.20/0.59            sk_D @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['158', '159'])).
% 0.20/0.59  thf('161', plain,
% 0.20/0.59      ((~ (v5_pre_topc @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E) @ 
% 0.20/0.59           sk_D @ sk_B))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               sk_D @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('162', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               sk_D @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['160', '161'])).
% 0.20/0.59  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('164', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               sk_D @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['162', '163'])).
% 0.20/0.59  thf('165', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('166', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               sk_D @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['164', '165'])).
% 0.20/0.59  thf('167', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('168', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               sk_D @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['166', '167'])).
% 0.20/0.59  thf('169', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('170', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_D @ sk_B)) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['168', '169'])).
% 0.20/0.59  thf('171', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('172', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('173', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (v5_pre_topc @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59             X4 @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('174', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (v5_pre_topc @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59             X4 @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['173'])).
% 0.20/0.59  thf('175', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v5_pre_topc @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           sk_C @ sk_B)
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['172', '174'])).
% 0.20/0.59  thf('176', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('178', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('179', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('180', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('181', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('183', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('184', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v5_pre_topc @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           sk_C @ sk_B)
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['175', '176', '177', '178', '179', '180', '181', '182', '183'])).
% 0.20/0.59  thf('185', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | (v5_pre_topc @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E) @ 
% 0.20/0.59            sk_C @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['171', '184'])).
% 0.20/0.59  thf('186', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('187', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v5_pre_topc @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E) @ 
% 0.20/0.59            sk_C @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['185', '186'])).
% 0.20/0.59  thf('188', plain,
% 0.20/0.59      ((~ (v5_pre_topc @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E) @ 
% 0.20/0.59           sk_C @ sk_B))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               sk_C @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('189', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               sk_C @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['187', '188'])).
% 0.20/0.59  thf('190', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('191', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               sk_C @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['189', '190'])).
% 0.20/0.59  thf('192', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('193', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               sk_C @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['191', '192'])).
% 0.20/0.59  thf('194', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('195', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               sk_C @ sk_B)) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['193', '194'])).
% 0.20/0.59  thf('196', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('197', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_C @ sk_B)) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['195', '196'])).
% 0.20/0.59  thf('198', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('199', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('200', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (v1_funct_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('201', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (v1_funct_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['200'])).
% 0.20/0.59  thf('202', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['199', '201'])).
% 0.20/0.59  thf('203', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('204', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('205', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('206', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('207', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('208', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('210', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('211', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['202', '203', '204', '205', '206', '207', '208', '209', '210'])).
% 0.20/0.59  thf('212', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | (v1_funct_1 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['198', '211'])).
% 0.20/0.59  thf('213', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('214', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v1_funct_1 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_D @ sk_E))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['212', '213'])).
% 0.20/0.59  thf('215', plain,
% 0.20/0.59      ((~ (v1_funct_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_D @ sk_E)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('216', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['214', '215'])).
% 0.20/0.59  thf('217', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('218', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['216', '217'])).
% 0.20/0.59  thf('219', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('220', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['218', '219'])).
% 0.20/0.59  thf('221', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('222', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['220', '221'])).
% 0.20/0.59  thf('223', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('224', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E))) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['222', '223'])).
% 0.20/0.59  thf('225', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('226', plain,
% 0.20/0.59      (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('227', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('228', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | (v1_funct_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('229', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | (v1_funct_1 @ 
% 0.20/0.59             (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['228'])).
% 0.20/0.59  thf('230', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59             (u1_struct_0 @ sk_B))
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['227', '229'])).
% 0.20/0.59  thf('231', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('232', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('233', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('234', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('235', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('236', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('237', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('238', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('239', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | ~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59        | (v1_funct_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E))
% 0.20/0.59        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['230', '231', '232', '233', '234', '235', '236', '237', '238'])).
% 0.20/0.59  thf('240', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | (v1_funct_1 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['226', '239'])).
% 0.20/0.59  thf('241', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v1_funct_1 @ 
% 0.20/0.59            (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59             sk_C @ sk_E))
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['225', '240'])).
% 0.20/0.59  thf('242', plain,
% 0.20/0.59      ((~ (v1_funct_1 @ 
% 0.20/0.59           (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59            sk_C @ sk_E)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('243', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['241', '242'])).
% 0.20/0.59  thf('244', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('245', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['243', '244'])).
% 0.20/0.59  thf('246', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('247', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['245', '246'])).
% 0.20/0.59  thf('248', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('249', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E))) & 
% 0.20/0.59             ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.59      inference('clc', [status(thm)], ['247', '248'])).
% 0.20/0.59  thf('250', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('251', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E))) | 
% 0.20/0.59       ~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['249', '250'])).
% 0.20/0.59  thf('252', plain,
% 0.20/0.59      (~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 0.20/0.59       ~
% 0.20/0.59       ((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.59       ~ ((v1_funct_1 @ sk_E)) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v1_funct_2 @ sk_E @ 
% 0.20/0.59         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59         (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ~
% 0.20/0.59       ((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_D @ sk_B)) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E))) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E))) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.59       ~
% 0.20/0.59       ((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_C @ sk_B)) | 
% 0.20/0.59       ~
% 0.20/0.59       ((m1_subset_1 @ sk_E @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59           (u1_struct_0 @ sk_B)))))),
% 0.20/0.59      inference('split', [status(esa)], ['43'])).
% 0.20/0.59  thf('253', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_D @ sk_B)
% 0.20/0.59        | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('254', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_D @ sk_B)) | 
% 0.20/0.59       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.59      inference('split', [status(esa)], ['253'])).
% 0.20/0.59  thf('255', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E))
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('256', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E)))
% 0.20/0.59         <= (((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E))))),
% 0.20/0.59      inference('split', [status(esa)], ['255'])).
% 0.20/0.59  thf('257', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E))
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('258', plain,
% 0.20/0.59      (((v1_funct_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E)))
% 0.20/0.59         <= (((v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E))))),
% 0.20/0.59      inference('split', [status(esa)], ['257'])).
% 0.20/0.59  thf('259', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_D @ sk_B)
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('260', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_D @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               sk_D @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['259'])).
% 0.20/0.59  thf('261', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_C @ sk_B)
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('262', plain,
% 0.20/0.59      (((v5_pre_topc @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         sk_C @ sk_B))
% 0.20/0.59         <= (((v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               sk_C @ sk_B)))),
% 0.20/0.59      inference('split', [status(esa)], ['261'])).
% 0.20/0.59  thf('263', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('264', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('split', [status(esa)], ['263'])).
% 0.20/0.59  thf('265', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('266', plain,
% 0.20/0.59      (((v1_funct_2 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))
% 0.20/0.59         <= (((v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('split', [status(esa)], ['265'])).
% 0.20/0.59  thf('267', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('268', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.20/0.59         <= (((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_D @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('split', [status(esa)], ['267'])).
% 0.20/0.59  thf('269', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59        | (v1_funct_1 @ sk_E))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('270', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.59          sk_E) @ 
% 0.20/0.59         (k1_zfmisc_1 @ 
% 0.20/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))
% 0.20/0.59         <= (((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('split', [status(esa)], ['269'])).
% 0.20/0.59  thf('271', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.59          | ~ (v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3))
% 0.20/0.59          | ~ (v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59               (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59               X4 @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ X3) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_1 @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3))
% 0.20/0.59          | ~ (v1_funct_2 @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v5_pre_topc @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59               X1 @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ X3) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.20/0.59          | (v5_pre_topc @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59                 (u1_struct_0 @ X0))))
% 0.20/0.59          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 0.20/0.59               (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ X3)
% 0.20/0.59          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.20/0.59          | ~ (m1_pre_topc @ X4 @ X2)
% 0.20/0.59          | (v2_struct_0 @ X4)
% 0.20/0.59          | ~ (l1_pre_topc @ X2)
% 0.20/0.59          | ~ (v2_pre_topc @ X2)
% 0.20/0.59          | (v2_struct_0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.20/0.59  thf('272', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.59         | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.20/0.59         | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59         | ~ (v1_funct_2 @ sk_E @ 
% 0.20/0.59              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59              (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (m1_subset_1 @ sk_E @ 
% 0.20/0.59              (k1_zfmisc_1 @ 
% 0.20/0.59               (k2_zfmisc_1 @ 
% 0.20/0.59                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59                (u1_struct_0 @ sk_B))))
% 0.20/0.59         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59         | ~ (m1_subset_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              (k1_zfmisc_1 @ 
% 0.20/0.59               (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59         | ~ (v5_pre_topc @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              sk_D @ sk_B)
% 0.20/0.59         | ~ (v1_funct_2 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (v1_funct_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E))
% 0.20/0.59         | ~ (v5_pre_topc @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E) @ 
% 0.20/0.59              sk_C @ sk_B)
% 0.20/0.59         | ~ (v1_funct_2 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E) @ 
% 0.20/0.59              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (v1_funct_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E))
% 0.20/0.59         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59         | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['270', '271'])).
% 0.20/0.59  thf('273', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('274', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('275', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('276', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.20/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('277', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('278', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59        (u1_struct_0 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('279', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.20/0.59          (u1_struct_0 @ sk_B))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('280', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('281', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('282', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('283', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59         | ~ (m1_subset_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              (k1_zfmisc_1 @ 
% 0.20/0.59               (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.59         | ~ (v5_pre_topc @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              sk_D @ sk_B)
% 0.20/0.59         | ~ (v1_funct_2 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (v1_funct_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E))
% 0.20/0.59         | ~ (v5_pre_topc @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E) @ 
% 0.20/0.59              sk_C @ sk_B)
% 0.20/0.59         | ~ (v1_funct_2 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E) @ 
% 0.20/0.59              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (v1_funct_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E))
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59                sk_C @ sk_E) @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['272', '273', '274', '275', '276', '277', '278', '279', 
% 0.20/0.59                 '280', '281', '282'])).
% 0.20/0.59  thf('284', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | ~ (v1_funct_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E))
% 0.20/0.59         | ~ (v1_funct_2 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E) @ 
% 0.20/0.59              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (v5_pre_topc @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_C @ sk_E) @ 
% 0.20/0.59              sk_C @ sk_B)
% 0.20/0.59         | ~ (v1_funct_1 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E))
% 0.20/0.59         | ~ (v1_funct_2 @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.59         | ~ (v5_pre_topc @ 
% 0.20/0.59              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.59               sk_D @ sk_E) @ 
% 0.20/0.59              sk_D @ sk_B)
% 0.20/0.59         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_C)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (((m1_subset_1 @ 
% 0.20/0.59               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['268', '283'])).
% 0.20/0.60  thf('285', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_A)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.60         | ~ (v5_pre_topc @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E) @ 
% 0.20/0.60              sk_D @ sk_B)
% 0.20/0.60         | ~ (v1_funct_2 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E) @ 
% 0.20/0.60              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E))
% 0.20/0.60         | ~ (v5_pre_topc @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_C @ sk_E) @ 
% 0.20/0.60              sk_C @ sk_B)
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_C @ sk_E))
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | (v2_struct_0 @ sk_B)))
% 0.20/0.60         <= (((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['266', '284'])).
% 0.20/0.60  thf('286', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_B)
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_C @ sk_E))
% 0.20/0.60         | ~ (v5_pre_topc @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_C @ sk_E) @ 
% 0.20/0.60              sk_C @ sk_B)
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E))
% 0.20/0.60         | ~ (v5_pre_topc @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E) @ 
% 0.20/0.60              sk_D @ sk_B)
% 0.20/0.60         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v2_struct_0 @ sk_A)))
% 0.20/0.60         <= (((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['264', '285'])).
% 0.20/0.60  thf('287', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_A)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.60         | ~ (v5_pre_topc @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E) @ 
% 0.20/0.60              sk_D @ sk_B)
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E))
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_C @ sk_E))
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | (v2_struct_0 @ sk_B)))
% 0.20/0.60         <= (((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['262', '286'])).
% 0.20/0.60  thf('288', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_B)
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_C @ sk_E))
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E))
% 0.20/0.60         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v2_struct_0 @ sk_A)))
% 0.20/0.60         <= (((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['260', '287'])).
% 0.20/0.60  thf('289', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_A)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.60         | ~ (v1_funct_1 @ 
% 0.20/0.60              (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60               sk_D @ sk_E))
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | (v2_struct_0 @ sk_B)))
% 0.20/0.60         <= (((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['258', '288'])).
% 0.20/0.60  thf('290', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_B)
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v2_struct_0 @ sk_A)))
% 0.20/0.60         <= (((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['256', '289'])).
% 0.20/0.60  thf('291', plain,
% 0.20/0.60      ((~ (v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.20/0.60         <= (~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.20/0.60      inference('split', [status(esa)], ['43'])).
% 0.20/0.60  thf('292', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_A)
% 0.20/0.60         | (v2_struct_0 @ sk_C)
% 0.20/0.60         | (v2_struct_0 @ sk_D)
% 0.20/0.60         | (v2_struct_0 @ sk_B)))
% 0.20/0.60         <= (~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['290', '291'])).
% 0.20/0.60  thf('293', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('294', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.60         <= (~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['292', '293'])).
% 0.20/0.60  thf('295', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('296', plain,
% 0.20/0.60      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.60         <= (~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('clc', [status(thm)], ['294', '295'])).
% 0.20/0.60  thf('297', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('298', plain,
% 0.20/0.60      (((v2_struct_0 @ sk_D))
% 0.20/0.60         <= (~ ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               sk_C @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_C @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) & 
% 0.20/0.60             ((v1_funct_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E))) & 
% 0.20/0.60             ((v1_funct_2 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.20/0.60             ((v5_pre_topc @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               sk_D @ sk_B)) & 
% 0.20/0.60             ((m1_subset_1 @ 
% 0.20/0.60               (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.60                sk_D @ sk_E) @ 
% 0.20/0.60               (k1_zfmisc_1 @ 
% 0.20/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.60      inference('clc', [status(thm)], ['296', '297'])).
% 0.20/0.60  thf('299', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('300', plain,
% 0.20/0.60      (~
% 0.20/0.60       ((v5_pre_topc @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.60          sk_E) @ 
% 0.20/0.60         sk_D @ sk_B)) | 
% 0.20/0.60       ~
% 0.20/0.60       ((m1_subset_1 @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.60          sk_E) @ 
% 0.20/0.60         (k1_zfmisc_1 @ 
% 0.20/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.60       ~
% 0.20/0.60       ((v1_funct_2 @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.60          sk_E) @ 
% 0.20/0.60         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.60       ~
% 0.20/0.60       ((v1_funct_1 @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.20/0.60          sk_E))) | 
% 0.20/0.60       ~
% 0.20/0.60       ((m1_subset_1 @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.60          sk_E) @ 
% 0.20/0.60         (k1_zfmisc_1 @ 
% 0.20/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.60       ~
% 0.20/0.60       ((v5_pre_topc @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.60          sk_E) @ 
% 0.20/0.60         sk_C @ sk_B)) | 
% 0.20/0.60       ~
% 0.20/0.60       ((v1_funct_2 @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.60          sk_E) @ 
% 0.20/0.60         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))) | 
% 0.20/0.60       ~
% 0.20/0.60       ((v1_funct_1 @ 
% 0.20/0.60         (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.20/0.60          sk_E))) | 
% 0.20/0.60       ((v5_pre_topc @ sk_E @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['298', '299'])).
% 0.20/0.60  thf('301', plain, ($false),
% 0.20/0.60      inference('sat_resolution*', [status(thm)],
% 0.20/0.60                ['1', '3', '5', '7', '9', '11', '13', '53', '56', '59', '62', 
% 0.20/0.60                 '89', '116', '143', '170', '197', '224', '251', '252', '254', 
% 0.20/0.60                 '300'])).
% 0.20/0.60  
% 0.20/0.60  % SZS output end Refutation
% 0.20/0.60  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
