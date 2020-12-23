%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fg4wDvGJUM

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:10 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  503 (3869 expanded)
%              Number of leaves         :   29 ( 982 expanded)
%              Depth                    :   62
%              Number of atoms          : 20201 (305577 expanded)
%              Number of equality atoms :  105 (2118 expanded)
%              Maximal formula depth    :   31 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r3_tsep_1_type,type,(
    r3_tsep_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(t137_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( A
                  = ( k1_tsep_1 @ A @ B @ C ) )
               => ( ( r3_tsep_1 @ A @ B @ C )
                <=> ( ( r1_tsep_1 @ B @ C )
                    & ! [D: $i] :
                        ( ( ~ ( v2_struct_0 @ D )
                          & ( v2_pre_topc @ D )
                          & ( l1_pre_topc @ D ) )
                       => ! [E: $i] :
                            ( ( ( v1_funct_1 @ E )
                              & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) )
                              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ D @ E @ B ) )
                                & ( v1_funct_2 @ ( k2_tmap_1 @ A @ D @ E @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ ( k2_tmap_1 @ A @ D @ E @ B ) @ B @ D )
                                & ( m1_subset_1 @ ( k2_tmap_1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) )
                                & ( v1_funct_1 @ ( k2_tmap_1 @ A @ D @ E @ C ) )
                                & ( v1_funct_2 @ ( k2_tmap_1 @ A @ D @ E @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ ( k2_tmap_1 @ A @ D @ E @ C ) @ C @ D )
                                & ( m1_subset_1 @ ( k2_tmap_1 @ A @ D @ E @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                             => ( ( v1_funct_1 @ E )
                                & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ E @ A @ D )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( A
                    = ( k1_tsep_1 @ A @ B @ C ) )
                 => ( ( r3_tsep_1 @ A @ B @ C )
                  <=> ( ( r1_tsep_1 @ B @ C )
                      & ! [D: $i] :
                          ( ( ~ ( v2_struct_0 @ D )
                            & ( v2_pre_topc @ D )
                            & ( l1_pre_topc @ D ) )
                         => ! [E: $i] :
                              ( ( ( v1_funct_1 @ E )
                                & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) )
                             => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ D @ E @ B ) )
                                  & ( v1_funct_2 @ ( k2_tmap_1 @ A @ D @ E @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ ( k2_tmap_1 @ A @ D @ E @ B ) @ B @ D )
                                  & ( m1_subset_1 @ ( k2_tmap_1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) )
                                  & ( v1_funct_1 @ ( k2_tmap_1 @ A @ D @ E @ C ) )
                                  & ( v1_funct_2 @ ( k2_tmap_1 @ A @ D @ E @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ ( k2_tmap_1 @ A @ D @ E @ C ) @ C @ D )
                                  & ( m1_subset_1 @ ( k2_tmap_1 @ A @ D @ E @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                               => ( ( v1_funct_1 @ E )
                                  & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ E @ A @ D )
                                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t137_tmap_1])).

thf('0',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf(t135_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r3_tsep_1 @ A @ B @ C )
              <=> ( ( r1_tsep_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v2_struct_0 @ D )
                        & ( v2_pre_topc @ D )
                        & ( l1_pre_topc @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) )
                              & ( v1_funct_2 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ B @ D )
                              & ( m1_subset_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) )
                              & ( v1_funct_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) )
                              & ( v1_funct_2 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ C @ D )
                              & ( m1_subset_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ( ( v1_funct_1 @ E )
                              & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ( r1_tsep_1 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
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
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ( v5_pre_topc @ X16 @ sk_A @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ! [X15: $i,X16: $i] :
        ( ( v2_struct_0 @ X15 )
        | ~ ( v2_pre_topc @ X15 )
        | ~ ( l1_pre_topc @ X15 )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_1 @ X16 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
        | ( v5_pre_topc @ X16 @ sk_A @ X15 ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v1_funct_1 @ ( sk_E @ X11 @ X9 @ X10 ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('59',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('60',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( l1_pre_topc @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v2_pre_topc @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v1_funct_2 @ ( sk_E @ X11 @ X9 @ X10 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('97',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( m1_subset_1 @ ( sk_E @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','106'])).

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

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['95','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['94','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['93','117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['92','119'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['91','121'])).

thf('123',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('124',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','106'])).

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

thf('130',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X7 )
      | ( ( k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) @ X8 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('131',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['126','135'])).

thf('137',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['125','137'])).

thf('139',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ( ( k3_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['124','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['123','145'])).

thf('147',plain,
    ( ( ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['122','146'])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('150',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ ( sk_E @ X11 @ X9 @ X10 ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','156'])).

thf('158',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['149','159'])).

thf('161',plain,
    ( ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['148','160'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['120'])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['144'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('172',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ ( sk_E @ X11 @ X9 @ X10 ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','178'])).

thf('180',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['171','181'])).

thf('183',plain,
    ( ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['170','182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','106'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('187',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('188',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ ( sk_E @ X11 @ X9 @ X10 ) ) @ X11 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['188','194'])).

thf('196',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['187','197'])).

thf('199',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['186','198'])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('202',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('203',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ ( sk_E @ X11 @ X9 @ X10 ) ) @ X9 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['203','209'])).

thf('211',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['202','212'])).

thf('214',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['201','213'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('217',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('218',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ ( sk_E @ X11 @ X9 @ X10 ) ) @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['218','224'])).

thf('226',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['217','227'])).

thf('229',plain,
    ( ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['216','228'])).

thf('230',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('232',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('233',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ ( sk_E @ X11 @ X9 @ X10 ) ) @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['233','239'])).

thf('241',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['232','242'])).

thf('244',plain,
    ( ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['231','243'])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('247',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('248',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ ( sk_E @ X11 @ X9 @ X10 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['248','254'])).

thf('256',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['247','257'])).

thf('259',plain,
    ( ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['246','258'])).

thf('260',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        = ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('262',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('263',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ ( sk_E @ X11 @ X9 @ X10 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['263','269'])).

thf('271',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['262','272'])).

thf('274',plain,
    ( ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['261','273'])).

thf('275',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,
    ( ! [X15: $i,X16: $i] :
        ( ( v2_struct_0 @ X15 )
        | ~ ( v2_pre_topc @ X15 )
        | ~ ( l1_pre_topc @ X15 )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_1 @ X16 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
        | ( v5_pre_topc @ X16 @ sk_A @ X15 ) )
   <= ! [X15: $i,X16: $i] :
        ( ( v2_struct_0 @ X15 )
        | ~ ( v2_pre_topc @ X15 )
        | ~ ( l1_pre_topc @ X15 )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_1 @ X16 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
        | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
        | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('277',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['260','278'])).

thf('280',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['245','280'])).

thf('282',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['230','282'])).

thf('284',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['215','284'])).

thf('286',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['200','286'])).

thf('288',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['185','288'])).

thf('290',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['184','290'])).

thf('292',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['162','292'])).

thf('294',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['90','294'])).

thf('296',plain,
    ( ( ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['295'])).

thf('297',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['78','296'])).

thf('298',plain,
    ( ( ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['68','298'])).

thf('300',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['58','300'])).

thf('302',plain,
    ( ( ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('304',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','106'])).

thf('305',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ~ ( v1_funct_1 @ ( sk_E @ X11 @ X9 @ X10 ) )
      | ~ ( v1_funct_2 @ ( sk_E @ X11 @ X9 @ X10 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ X11 @ X9 @ X10 ) @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ ( sk_E @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) @ ( u1_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) ) ) ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('307',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['307','308','309','310','311','312','313'])).

thf('315',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['304','314'])).

thf('316',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('317',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,
    ( ( ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['303','318'])).

thf('320',plain,
    ( ( ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['302','320'])).

thf('322',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['57','322'])).

thf('324',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r1_tsep_1 @ X9 @ X11 )
      | ~ ( v2_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('326',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['324','325'])).

thf('327',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('331',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(demod,[status(thm)],['326','327','328','329','330','331'])).

thf('333',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('335',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(clc,[status(thm)],['335','336'])).

thf('338',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) ) ) ),
    inference(clc,[status(thm)],['337','338'])).

thf('340',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( ~ ! [X15: $i,X16: $i] :
          ( ( v2_struct_0 @ X15 )
          | ~ ( v2_pre_topc @ X15 )
          | ~ ( l1_pre_topc @ X15 )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ sk_B @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) )
          | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) )
          | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ sk_C @ X15 )
          | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_1 @ X16 )
          | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) ) ) )
          | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X15 ) )
          | ( v5_pre_topc @ X16 @ sk_A @ X15 ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['342'])).

thf('344',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('345',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['16'])).

thf('346',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['342'])).

thf('348',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('349',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('350',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('351',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('352',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('353',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(demod,[status(thm)],['353','354','355'])).

thf('357',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['350','356'])).

thf('358',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['349','357'])).

thf('359',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['348','358'])).

thf('360',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['347','359'])).

thf('361',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['346','360'])).

thf('362',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ( ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['361','362'])).

thf('364',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('366',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['342'])).

thf('367',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('368',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('369',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('370',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('371',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X7 )
      | ( ( k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) @ X8 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('372',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( ( k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['370','371'])).

thf('373',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( ( k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['369','372'])).

thf('374',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ( ( k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['368','373'])).

thf('375',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ( ( k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['367','374'])).

thf('376',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_A @ X0 )
        | ( ( k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
        | ~ ( m1_pre_topc @ X1 @ sk_A )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['366','375'])).

thf('377',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['365','376'])).

thf('378',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['377','378','379','380'])).

thf('382',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['381'])).

thf('383',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['364','382'])).

thf('384',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ( ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['383','384'])).

thf('386',plain,
    ( ( ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['363','385'])).

thf('387',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('388',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['347','359'])).

thf('390',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( ( ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['390','391'])).

thf('393',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['381'])).

thf('395',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['393','394'])).

thf('396',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['395','396'])).

thf('398',plain,
    ( ( ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['392','397'])).

thf('399',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['398'])).

thf('400',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('401',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['12'])).

thf('402',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('403',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['398'])).

thf('404',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('405',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('406',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('407',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['398'])).

thf('408',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('409',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('410',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['398'])).

thf('411',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 )
        = ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('412',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('413',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( r3_tsep_1 @ X10 @ X9 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X13 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ X12 ) @ X11 @ X13 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ X12 ) @ X9 @ X13 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ X12 ) @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X10 @ X13 @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X9 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('415',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ X1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ X1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ X1 ) @ sk_C @ X0 )
      | ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['413','414'])).

thf('416',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('417',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('420',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) @ sk_C @ X0 )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['415','416','417','418','419','420','421','422','423','424','425','426','427','428','429'])).

thf('431',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) ) ) )
        | ( v5_pre_topc @ X0 @ sk_A @ X1 )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0 ) @ sk_C @ X1 )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0 ) )
        | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X1 ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0 ) @ sk_B @ X1 )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0 ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) ) ) ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['412','430'])).

thf('432',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['411','431'])).

thf('433',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('434',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['342'])).

thf('435',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('436',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('437',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('438',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['432','433','434','435','436','437'])).

thf('439',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['438'])).

thf('440',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['410','439'])).

thf('441',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['440'])).

thf('442',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['409','441'])).

thf('443',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['408','442'])).

thf('444',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['407','443'])).

thf('445',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['444'])).

thf('446',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['406','445'])).

thf('447',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['446'])).

thf('448',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['405','447'])).

thf('449',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) @ sk_C @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['404','448'])).

thf('450',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['403','449'])).

thf('451',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) @ sk_B @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['450'])).

thf('452',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['402','451'])).

thf('453',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['452'])).

thf('454',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['401','453'])).

thf('455',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['400','454'])).

thf('456',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['399','455'])).

thf('457',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['456'])).

thf('458',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['387','457'])).

thf('459',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['458'])).

thf('460',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['345','459'])).

thf('461',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['344','460'])).

thf('462',plain,
    ( ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
   <= ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('463',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('464',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('465',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['463','464'])).

thf('466',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('467',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['465','466'])).

thf('468',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['467','468'])).

thf('470',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('471',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C ) @ sk_C @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['469','470'])).

thf('472',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','13','15','17','19','21','23','25','27','44','45','47','341','343','471'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fg4wDvGJUM
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:22:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.85  % Solved by: fo/fo7.sh
% 0.60/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.85  % done 447 iterations in 0.358s
% 0.60/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.85  % SZS output start Refutation
% 0.60/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.85  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.60/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.85  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.60/0.85  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.60/0.85  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.60/0.85  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.60/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.85  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.60/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.85  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.60/0.85  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.60/0.85  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.60/0.85  thf(r3_tsep_1_type, type, r3_tsep_1: $i > $i > $i > $o).
% 0.60/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.85  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.60/0.85  thf(t137_tmap_1, conjecture,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.85               ( ( ( A ) = ( k1_tsep_1 @ A @ B @ C ) ) =>
% 0.60/0.85                 ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 0.60/0.85                   ( ( r1_tsep_1 @ B @ C ) & 
% 0.60/0.85                     ( ![D:$i]:
% 0.60/0.85                       ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 0.60/0.85                           ( l1_pre_topc @ D ) ) =>
% 0.60/0.85                         ( ![E:$i]:
% 0.60/0.85                           ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                               ( v1_funct_2 @
% 0.60/0.85                                 E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                               ( m1_subset_1 @
% 0.60/0.85                                 E @ 
% 0.60/0.85                                 ( k1_zfmisc_1 @
% 0.60/0.85                                   ( k2_zfmisc_1 @
% 0.60/0.85                                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.60/0.85                             ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ D @ E @ B ) ) & 
% 0.60/0.85                                 ( v1_funct_2 @
% 0.60/0.85                                   ( k2_tmap_1 @ A @ D @ E @ B ) @ 
% 0.60/0.85                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                 ( v5_pre_topc @
% 0.60/0.85                                   ( k2_tmap_1 @ A @ D @ E @ B ) @ B @ D ) & 
% 0.60/0.85                                 ( m1_subset_1 @
% 0.60/0.85                                   ( k2_tmap_1 @ A @ D @ E @ B ) @ 
% 0.60/0.85                                   ( k1_zfmisc_1 @
% 0.60/0.85                                     ( k2_zfmisc_1 @
% 0.60/0.85                                       ( u1_struct_0 @ B ) @ 
% 0.60/0.85                                       ( u1_struct_0 @ D ) ) ) ) & 
% 0.60/0.85                                 ( v1_funct_1 @ ( k2_tmap_1 @ A @ D @ E @ C ) ) & 
% 0.60/0.85                                 ( v1_funct_2 @
% 0.60/0.85                                   ( k2_tmap_1 @ A @ D @ E @ C ) @ 
% 0.60/0.85                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                 ( v5_pre_topc @
% 0.60/0.85                                   ( k2_tmap_1 @ A @ D @ E @ C ) @ C @ D ) & 
% 0.60/0.85                                 ( m1_subset_1 @
% 0.60/0.85                                   ( k2_tmap_1 @ A @ D @ E @ C ) @ 
% 0.60/0.85                                   ( k1_zfmisc_1 @
% 0.60/0.85                                     ( k2_zfmisc_1 @
% 0.60/0.85                                       ( u1_struct_0 @ C ) @ 
% 0.60/0.85                                       ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.60/0.85                               ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                                 ( v1_funct_2 @
% 0.60/0.85                                   E @ ( u1_struct_0 @ A ) @ 
% 0.60/0.85                                   ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                 ( v5_pre_topc @ E @ A @ D ) & 
% 0.60/0.85                                 ( m1_subset_1 @
% 0.60/0.85                                   E @ 
% 0.60/0.85                                   ( k1_zfmisc_1 @
% 0.60/0.85                                     ( k2_zfmisc_1 @
% 0.60/0.85                                       ( u1_struct_0 @ A ) @ 
% 0.60/0.85                                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.85    (~( ![A:$i]:
% 0.60/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.85            ( l1_pre_topc @ A ) ) =>
% 0.60/0.85          ( ![B:$i]:
% 0.60/0.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.85              ( ![C:$i]:
% 0.60/0.85                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.85                  ( ( ( A ) = ( k1_tsep_1 @ A @ B @ C ) ) =>
% 0.60/0.85                    ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 0.60/0.85                      ( ( r1_tsep_1 @ B @ C ) & 
% 0.60/0.85                        ( ![D:$i]:
% 0.60/0.85                          ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 0.60/0.85                              ( l1_pre_topc @ D ) ) =>
% 0.60/0.85                            ( ![E:$i]:
% 0.60/0.85                              ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                                  ( v1_funct_2 @
% 0.60/0.85                                    E @ ( u1_struct_0 @ A ) @ 
% 0.60/0.85                                    ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                  ( m1_subset_1 @
% 0.60/0.85                                    E @ 
% 0.60/0.85                                    ( k1_zfmisc_1 @
% 0.60/0.85                                      ( k2_zfmisc_1 @
% 0.60/0.85                                        ( u1_struct_0 @ A ) @ 
% 0.60/0.85                                        ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.60/0.85                                ( ( ( v1_funct_1 @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ B ) ) & 
% 0.60/0.85                                    ( v1_funct_2 @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ B ) @ 
% 0.60/0.85                                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                    ( v5_pre_topc @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ B ) @ B @ D ) & 
% 0.60/0.85                                    ( m1_subset_1 @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ B ) @ 
% 0.60/0.85                                      ( k1_zfmisc_1 @
% 0.60/0.85                                        ( k2_zfmisc_1 @
% 0.60/0.85                                          ( u1_struct_0 @ B ) @ 
% 0.60/0.85                                          ( u1_struct_0 @ D ) ) ) ) & 
% 0.60/0.85                                    ( v1_funct_1 @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ C ) ) & 
% 0.60/0.85                                    ( v1_funct_2 @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ C ) @ 
% 0.60/0.85                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                    ( v5_pre_topc @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ C ) @ C @ D ) & 
% 0.60/0.85                                    ( m1_subset_1 @
% 0.60/0.85                                      ( k2_tmap_1 @ A @ D @ E @ C ) @ 
% 0.60/0.85                                      ( k1_zfmisc_1 @
% 0.60/0.85                                        ( k2_zfmisc_1 @
% 0.60/0.85                                          ( u1_struct_0 @ C ) @ 
% 0.60/0.85                                          ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.60/0.85                                  ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                                    ( v1_funct_2 @
% 0.60/0.85                                      E @ ( u1_struct_0 @ A ) @ 
% 0.60/0.85                                      ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                                    ( v5_pre_topc @ E @ A @ D ) & 
% 0.60/0.85                                    ( m1_subset_1 @
% 0.60/0.85                                      E @ 
% 0.60/0.85                                      ( k1_zfmisc_1 @
% 0.60/0.85                                        ( k2_zfmisc_1 @
% 0.60/0.85                                          ( u1_struct_0 @ A ) @ 
% 0.60/0.85                                          ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.85    inference('cnf.neg', [status(esa)], [t137_tmap_1])).
% 0.60/0.85  thf('0', plain,
% 0.60/0.85      ((~ (v2_struct_0 @ sk_D_1)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('1', plain,
% 0.60/0.85      (~ ((v2_struct_0 @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_B @ sk_C)) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['0'])).
% 0.60/0.85  thf('2', plain,
% 0.60/0.85      ((~ (m1_subset_1 @ sk_E_1 @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))
% 0.60/0.85        | ~ (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.60/0.85        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85             (u1_struct_0 @ sk_D_1))
% 0.60/0.85        | ~ (v1_funct_1 @ sk_E_1)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('3', plain,
% 0.60/0.85      (~ ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C)) | 
% 0.60/0.85       ~ ((v1_funct_1 @ sk_E_1)) | 
% 0.60/0.85       ~
% 0.60/0.85       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))) | 
% 0.60/0.85       ~
% 0.60/0.85       ((m1_subset_1 @ sk_E_1 @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))))),
% 0.60/0.85      inference('split', [status(esa)], ['2'])).
% 0.60/0.85  thf('4', plain,
% 0.60/0.85      (((v2_pre_topc @ sk_D_1)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('5', plain,
% 0.60/0.85      (((v2_pre_topc @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 0.60/0.85       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['4'])).
% 0.60/0.85  thf('6', plain,
% 0.60/0.85      (((v1_funct_1 @ sk_E_1)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('7', plain,
% 0.60/0.85      (((v1_funct_1 @ sk_E_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 0.60/0.85       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['6'])).
% 0.60/0.85  thf('8', plain,
% 0.60/0.85      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('9', plain,
% 0.60/0.85      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['8'])).
% 0.60/0.85  thf('10', plain,
% 0.60/0.85      (((m1_subset_1 @ sk_E_1 @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('11', plain,
% 0.60/0.85      (((m1_subset_1 @ sk_E_1 @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['10'])).
% 0.60/0.85  thf('12', plain,
% 0.60/0.85      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ sk_C @ 
% 0.60/0.85         sk_D_1)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('13', plain,
% 0.60/0.85      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ sk_C @ 
% 0.60/0.85         sk_D_1)) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['12'])).
% 0.60/0.85  thf('14', plain,
% 0.60/0.85      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.60/0.85         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('15', plain,
% 0.60/0.85      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.60/0.85         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['14'])).
% 0.60/0.85  thf('16', plain,
% 0.60/0.85      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('17', plain,
% 0.60/0.85      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['16'])).
% 0.60/0.85  thf('18', plain,
% 0.60/0.85      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('19', plain,
% 0.60/0.85      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['18'])).
% 0.60/0.85  thf('20', plain,
% 0.60/0.85      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ sk_B @ 
% 0.60/0.85         sk_D_1)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('21', plain,
% 0.60/0.85      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ sk_B @ 
% 0.60/0.85         sk_D_1)) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['20'])).
% 0.60/0.85  thf('22', plain,
% 0.60/0.85      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.60/0.85         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('23', plain,
% 0.60/0.85      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.60/0.85         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['22'])).
% 0.60/0.85  thf('24', plain,
% 0.60/0.85      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('25', plain,
% 0.60/0.85      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['24'])).
% 0.60/0.85  thf('26', plain,
% 0.60/0.85      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('27', plain,
% 0.60/0.85      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 0.60/0.85       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['26'])).
% 0.60/0.85  thf('28', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C) | (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('29', plain,
% 0.60/0.85      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.60/0.85         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf(t135_tmap_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.85               ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 0.60/0.85                 ( ( r1_tsep_1 @ B @ C ) & 
% 0.60/0.85                   ( ![D:$i]:
% 0.60/0.85                     ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 0.60/0.85                         ( l1_pre_topc @ D ) ) =>
% 0.60/0.85                       ( ![E:$i]:
% 0.60/0.85                         ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                             ( v1_funct_2 @
% 0.60/0.85                               E @ 
% 0.60/0.85                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 0.60/0.85                               ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                             ( m1_subset_1 @
% 0.60/0.85                               E @ 
% 0.60/0.85                               ( k1_zfmisc_1 @
% 0.60/0.85                                 ( k2_zfmisc_1 @
% 0.60/0.85                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 0.60/0.85                                   ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.60/0.85                           ( ( ( v1_funct_1 @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) ) & 
% 0.60/0.85                               ( v1_funct_2 @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 0.60/0.85                                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                               ( v5_pre_topc @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 0.60/0.85                                 B @ D ) & 
% 0.60/0.85                               ( m1_subset_1 @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 0.60/0.85                                 ( k1_zfmisc_1 @
% 0.60/0.85                                   ( k2_zfmisc_1 @
% 0.60/0.85                                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) & 
% 0.60/0.85                               ( v1_funct_1 @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) ) & 
% 0.60/0.85                               ( v1_funct_2 @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 0.60/0.85                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                               ( v5_pre_topc @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 0.60/0.85                                 C @ D ) & 
% 0.60/0.85                               ( m1_subset_1 @
% 0.60/0.85                                 ( k3_tmap_1 @
% 0.60/0.85                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 0.60/0.85                                 ( k1_zfmisc_1 @
% 0.60/0.85                                   ( k2_zfmisc_1 @
% 0.60/0.85                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.60/0.85                             ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                               ( v1_funct_2 @
% 0.60/0.85                                 E @ 
% 0.60/0.85                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 0.60/0.85                                 ( u1_struct_0 @ D ) ) & 
% 0.60/0.85                               ( v5_pre_topc @
% 0.60/0.85                                 E @ ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 0.60/0.85                               ( m1_subset_1 @
% 0.60/0.85                                 E @ 
% 0.60/0.85                                 ( k1_zfmisc_1 @
% 0.60/0.85                                   ( k2_zfmisc_1 @
% 0.60/0.85                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 0.60/0.85                                     ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('30', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X9)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ~ (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.85          | (r1_tsep_1 @ X9 @ X11)
% 0.60/0.85          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.85          | (v2_struct_0 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.85  thf('31', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85         | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.60/0.85         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.85  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('36', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.85      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.60/0.85  thf('37', plain,
% 0.60/0.85      ((~ (r1_tsep_1 @ sk_B @ sk_C)) <= (~ ((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['6'])).
% 0.60/0.85  thf('38', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.60/0.85         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.85  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('40', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.60/0.85         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['38', '39'])).
% 0.60/0.85  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('42', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_C))
% 0.60/0.85         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['40', '41'])).
% 0.60/0.85  thf('43', plain, (~ (v2_struct_0 @ sk_C)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('44', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) | ((r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf('46', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X15)
% 0.60/0.85          | ~ (v2_pre_topc @ X15)
% 0.60/0.85          | ~ (l1_pre_topc @ X15)
% 0.60/0.85          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.85               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.85          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ sk_B @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))))
% 0.60/0.85          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.85               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.60/0.85          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ sk_C @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))))
% 0.60/0.85          | (v5_pre_topc @ X16 @ sk_A @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))))
% 0.60/0.85          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))
% 0.60/0.85          | ~ (v1_funct_1 @ X16)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      ((![X15 : $i, X16 : $i]:
% 0.60/0.85          ((v2_struct_0 @ X15)
% 0.60/0.85           | ~ (v2_pre_topc @ X15)
% 0.60/0.85           | ~ (l1_pre_topc @ X15)
% 0.60/0.85           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.85           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.85                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.85           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ sk_B @ 
% 0.60/0.85                X15)
% 0.60/0.85           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.85                (k1_zfmisc_1 @ 
% 0.60/0.85                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))))
% 0.60/0.85           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.60/0.85           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.85                (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.60/0.85           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ sk_C @ 
% 0.60/0.85                X15)
% 0.60/0.85           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.85                (k1_zfmisc_1 @ 
% 0.60/0.85                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))))
% 0.60/0.85           | ~ (v1_funct_1 @ X16)
% 0.60/0.85           | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.85                (k1_zfmisc_1 @ 
% 0.60/0.85                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))))
% 0.60/0.85           | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))
% 0.60/0.85           | (v5_pre_topc @ X16 @ sk_A @ X15))) | 
% 0.60/0.85       ((r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('split', [status(esa)], ['46'])).
% 0.60/0.85  thf('48', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('51', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X9)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.85          | (v1_funct_1 @ (sk_E @ X11 @ X9 @ X10))
% 0.60/0.85          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.85          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.85          | (v2_struct_0 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.85  thf('52', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (v1_funct_1 @ (sk_E @ X0 @ sk_B @ sk_A))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.85  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('55', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (v1_funct_1 @ (sk_E @ X0 @ sk_B @ sk_A))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['49', '55'])).
% 0.60/0.85  thf('57', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['48', '56'])).
% 0.60/0.85  thf('58', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['48', '56'])).
% 0.60/0.85  thf('59', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf('60', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X9)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.85          | (l1_pre_topc @ (sk_D @ X11 @ X9 @ X10))
% 0.60/0.85          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.85          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.85          | (v2_struct_0 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.85  thf('63', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (l1_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['61', '62'])).
% 0.60/0.85  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('66', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (l1_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.60/0.85  thf('67', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['60', '66'])).
% 0.60/0.85  thf('68', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['59', '67'])).
% 0.60/0.85  thf('69', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('72', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X9)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.85          | (v2_pre_topc @ (sk_D @ X11 @ X9 @ X10))
% 0.60/0.85          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.85          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.85          | (v2_struct_0 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.85  thf('73', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (v2_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['71', '72'])).
% 0.60/0.85  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('76', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (v2_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.60/0.85  thf('77', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['70', '76'])).
% 0.60/0.85  thf('78', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['69', '77'])).
% 0.60/0.85  thf('79', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('82', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X9)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.85          | (v1_funct_2 @ (sk_E @ X11 @ X9 @ X10) @ 
% 0.60/0.85             (u1_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)) @ 
% 0.60/0.85             (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))
% 0.60/0.85          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.85          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.85          | (v2_struct_0 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.85  thf('83', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (v1_funct_2 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.85             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 0.60/0.85             (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['81', '82'])).
% 0.60/0.85  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('86', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (v1_funct_2 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.85             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 0.60/0.85             (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.60/0.85  thf('87', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.60/0.85           (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['80', '86'])).
% 0.60/0.85  thf('88', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('89', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85           (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['87', '88'])).
% 0.60/0.85  thf('90', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['79', '89'])).
% 0.60/0.85  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('92', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['48', '56'])).
% 0.60/0.85  thf('93', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['59', '67'])).
% 0.60/0.85  thf('94', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['69', '77'])).
% 0.60/0.85  thf('95', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['79', '89'])).
% 0.60/0.85  thf('96', plain,
% 0.60/0.85      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('split', [status(esa)], ['28'])).
% 0.60/0.85  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('98', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('99', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X9)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.85          | (m1_subset_1 @ (sk_E @ X11 @ X9 @ X10) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)) @ 
% 0.60/0.85               (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))))
% 0.60/0.85          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.85          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.85          | (v2_struct_0 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.85  thf('100', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 0.60/0.85               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['98', '99'])).
% 0.60/0.85  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('103', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.85          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 0.60/0.85               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 0.60/0.85          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.60/0.85  thf('104', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.60/0.85             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['97', '103'])).
% 0.60/0.85  thf('105', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('106', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.85        | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.85        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['104', '105'])).
% 0.60/0.85  thf('107', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85            (k1_zfmisc_1 @ 
% 0.60/0.85             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['96', '106'])).
% 0.60/0.85  thf(d4_tmap_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85             ( l1_pre_topc @ B ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( ( v1_funct_1 @ C ) & 
% 0.60/0.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                 ( m1_subset_1 @
% 0.60/0.85                   C @ 
% 0.60/0.85                   ( k1_zfmisc_1 @
% 0.60/0.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( m1_pre_topc @ D @ A ) =>
% 0.60/0.85                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.60/0.85                     ( k2_partfun1 @
% 0.60/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.60/0.85                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('108', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X2)
% 0.60/0.85          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.60/0.85                 (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_subset_1 @ X3 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.60/0.85          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.60/0.85          | ~ (v1_funct_1 @ X3)
% 0.60/0.85          | ~ (l1_pre_topc @ X2)
% 0.60/0.85          | ~ (v2_pre_topc @ X2)
% 0.60/0.85          | (v2_struct_0 @ X2))),
% 0.60/0.85      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.60/0.85  thf('109', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85           | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['107', '108'])).
% 0.60/0.85  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('112', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.60/0.85  thf('113', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['112'])).
% 0.60/0.85  thf('114', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['95', '113'])).
% 0.60/0.85  thf('115', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['114'])).
% 0.60/0.85  thf('116', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['94', '115'])).
% 0.60/0.85  thf('117', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['116'])).
% 0.60/0.85  thf('118', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['93', '117'])).
% 0.60/0.85  thf('119', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['118'])).
% 0.60/0.85  thf('120', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['92', '119'])).
% 0.60/0.85  thf('121', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['120'])).
% 0.60/0.85  thf('122', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_B)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (v2_struct_0 @ sk_A)
% 0.60/0.85         | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.60/0.85             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_C)))
% 0.60/0.85         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['91', '121'])).
% 0.60/0.85  thf('123', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t2_tsep_1, axiom,
% 0.60/0.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.60/0.85  thf('124', plain,
% 0.60/0.85      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('125', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['69', '77'])).
% 0.60/0.85  thf('126', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['59', '67'])).
% 0.60/0.85  thf('127', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['48', '56'])).
% 0.60/0.85  thf('128', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['79', '89'])).
% 0.60/0.85  thf('129', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85            (k1_zfmisc_1 @ 
% 0.60/0.85             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.85         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['96', '106'])).
% 0.60/0.85  thf(d5_tmap_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85             ( l1_pre_topc @ B ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( m1_pre_topc @ C @ A ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( m1_pre_topc @ D @ A ) =>
% 0.60/0.85                   ( ![E:$i]:
% 0.60/0.85                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                         ( v1_funct_2 @
% 0.60/0.85                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                         ( m1_subset_1 @
% 0.60/0.85                           E @ 
% 0.60/0.85                           ( k1_zfmisc_1 @
% 0.60/0.85                             ( k2_zfmisc_1 @
% 0.60/0.85                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85                       ( ( m1_pre_topc @ D @ C ) =>
% 0.60/0.85                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.60/0.85                           ( k2_partfun1 @
% 0.60/0.85                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.60/0.85                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('130', plain,
% 0.60/0.85      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X4)
% 0.60/0.85          | ~ (v2_pre_topc @ X4)
% 0.60/0.85          | ~ (l1_pre_topc @ X4)
% 0.60/0.85          | ~ (m1_pre_topc @ X5 @ X6)
% 0.60/0.85          | ~ (m1_pre_topc @ X5 @ X7)
% 0.60/0.85          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 0.60/0.85                 (u1_struct_0 @ X5)))
% 0.60/0.85          | ~ (m1_subset_1 @ X8 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 0.60/0.85          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 0.60/0.85          | ~ (v1_funct_1 @ X8)
% 0.60/0.85          | ~ (m1_pre_topc @ X7 @ X6)
% 0.60/0.85          | ~ (l1_pre_topc @ X6)
% 0.60/0.85          | ~ (v2_pre_topc @ X6)
% 0.60/0.85          | (v2_struct_0 @ X6))),
% 0.60/0.85      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.60/0.85  thf('131', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['129', '130'])).
% 0.60/0.85  thf('132', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | (v2_struct_0 @ X0)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['128', '131'])).
% 0.60/0.85  thf('133', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['132'])).
% 0.60/0.85  thf('134', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | (v2_struct_0 @ X0)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['127', '133'])).
% 0.60/0.85  thf('135', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['134'])).
% 0.60/0.85  thf('136', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | (v2_struct_0 @ X0)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['126', '135'])).
% 0.60/0.85  thf('137', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['136'])).
% 0.60/0.85  thf('138', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | (v2_struct_0 @ X0)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['125', '137'])).
% 0.60/0.85  thf('139', plain,
% 0.60/0.85      ((![X0 : $i, X1 : $i]:
% 0.60/0.85          ((v2_struct_0 @ X0)
% 0.60/0.85           | ~ (v2_pre_topc @ X0)
% 0.60/0.85           | ~ (l1_pre_topc @ X0)
% 0.60/0.85           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85           | ((k3_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X1 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X1)))
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['138'])).
% 0.60/0.85  thf('140', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          (~ (l1_pre_topc @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85           | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_A)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['124', '139'])).
% 0.60/0.85  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('144', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          ((v2_struct_0 @ sk_B)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0 @ 
% 0.60/0.85               (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | (v2_struct_0 @ sk_A)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.60/0.85  thf('145', plain,
% 0.60/0.85      ((![X0 : $i]:
% 0.60/0.85          (((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0 @ 
% 0.60/0.85             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.85           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85           | (v2_struct_0 @ sk_A)
% 0.60/0.85           | (v2_struct_0 @ sk_C)
% 0.60/0.85           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85           | (v2_struct_0 @ sk_B)))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['144'])).
% 0.60/0.85  thf('146', plain,
% 0.60/0.85      ((((v2_struct_0 @ sk_B)
% 0.60/0.85         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.85         | (v2_struct_0 @ sk_C)
% 0.60/0.85         | (v2_struct_0 @ sk_A)
% 0.60/0.85         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.85         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.85             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.85             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.85                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.85                (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_C)))))
% 0.60/0.85         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['123', '145'])).
% 0.60/0.86  thf('147', plain,
% 0.60/0.86      (((((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86           = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['122', '146'])).
% 0.60/0.86  thf('148', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['147'])).
% 0.60/0.86  thf('149', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('150', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('151', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('152', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (v1_funct_1 @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ (sk_E @ X11 @ X9 @ X10)))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('153', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['151', '152'])).
% 0.60/0.86  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('156', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.60/0.86  thf('157', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['150', '156'])).
% 0.60/0.86  thf('158', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('159', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['157', '158'])).
% 0.60/0.86  thf('160', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v1_funct_1 @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['149', '159'])).
% 0.60/0.86  thf('161', plain,
% 0.60/0.86      ((((v1_funct_1 @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['148', '160'])).
% 0.60/0.86  thf('162', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v1_funct_1 @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['161'])).
% 0.60/0.86  thf('163', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('164', plain,
% 0.60/0.86      ((![X0 : $i]:
% 0.60/0.86          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86           | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 0.60/0.86               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86                  (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.86           | (v2_struct_0 @ sk_A)
% 0.60/0.86           | (v2_struct_0 @ sk_C)
% 0.60/0.86           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86           | (v2_struct_0 @ sk_B)))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['120'])).
% 0.60/0.86  thf('165', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | ((k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.60/0.86             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['163', '164'])).
% 0.60/0.86  thf('166', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('167', plain,
% 0.60/0.86      ((![X0 : $i]:
% 0.60/0.86          (((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0 @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ X0)))
% 0.60/0.86           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86           | (v2_struct_0 @ sk_A)
% 0.60/0.86           | (v2_struct_0 @ sk_C)
% 0.60/0.86           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86           | (v2_struct_0 @ sk_B)))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['144'])).
% 0.60/0.86  thf('168', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['166', '167'])).
% 0.60/0.86  thf('169', plain,
% 0.60/0.86      (((((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86           = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['165', '168'])).
% 0.60/0.86  thf('170', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['169'])).
% 0.60/0.86  thf('171', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('172', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('173', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('174', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (v1_funct_1 @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ (sk_E @ X11 @ X9 @ X10)))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('175', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['173', '174'])).
% 0.60/0.86  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('178', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.60/0.86  thf('179', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['172', '178'])).
% 0.60/0.86  thf('180', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('181', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['179', '180'])).
% 0.60/0.86  thf('182', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v1_funct_1 @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['171', '181'])).
% 0.60/0.86  thf('183', plain,
% 0.60/0.86      ((((v1_funct_1 @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['170', '182'])).
% 0.60/0.86  thf('184', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v1_funct_1 @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['183'])).
% 0.60/0.86  thf('185', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_zfmisc_1 @ 
% 0.60/0.86             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['96', '106'])).
% 0.60/0.86  thf('186', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['147'])).
% 0.60/0.86  thf('187', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('188', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('189', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('190', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (v5_pre_topc @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ (sk_E @ X11 @ X9 @ X10)) @ 
% 0.60/0.86             X11 @ (sk_D @ X11 @ X9 @ X10))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('191', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v5_pre_topc @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['189', '190'])).
% 0.60/0.86  thf('192', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('193', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('194', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v5_pre_topc @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.60/0.86  thf('195', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v5_pre_topc @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['188', '194'])).
% 0.60/0.86  thf('196', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('197', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v5_pre_topc @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['195', '196'])).
% 0.60/0.86  thf('198', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v5_pre_topc @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86            sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['187', '197'])).
% 0.60/0.86  thf('199', plain,
% 0.60/0.86      ((((v5_pre_topc @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86          sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['186', '198'])).
% 0.60/0.86  thf('200', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v5_pre_topc @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86            sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['199'])).
% 0.60/0.86  thf('201', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['169'])).
% 0.60/0.86  thf('202', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('203', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('204', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('205', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (v5_pre_topc @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ (sk_E @ X11 @ X9 @ X10)) @ 
% 0.60/0.86             X9 @ (sk_D @ X11 @ X9 @ X10))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('206', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v5_pre_topc @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['204', '205'])).
% 0.60/0.86  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('209', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v5_pre_topc @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['206', '207', '208'])).
% 0.60/0.86  thf('210', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v5_pre_topc @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['203', '209'])).
% 0.60/0.86  thf('211', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('212', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v5_pre_topc @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['210', '211'])).
% 0.60/0.86  thf('213', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v5_pre_topc @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86            sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['202', '212'])).
% 0.60/0.86  thf('214', plain,
% 0.60/0.86      ((((v5_pre_topc @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86          sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['201', '213'])).
% 0.60/0.86  thf('215', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v5_pre_topc @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86            sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['214'])).
% 0.60/0.86  thf('216', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['147'])).
% 0.60/0.86  thf('217', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('218', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('219', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('220', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (v1_funct_2 @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ (sk_E @ X11 @ X9 @ X10)) @ 
% 0.60/0.86             (u1_struct_0 @ X11) @ (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('221', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_2 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['219', '220'])).
% 0.60/0.86  thf('222', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('223', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('224', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_2 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['221', '222', '223'])).
% 0.60/0.86  thf('225', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_2 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['218', '224'])).
% 0.60/0.86  thf('226', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('227', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_2 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['225', '226'])).
% 0.60/0.86  thf('228', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v1_funct_2 @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['217', '227'])).
% 0.60/0.86  thf('229', plain,
% 0.60/0.86      ((((v1_funct_2 @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['216', '228'])).
% 0.60/0.86  thf('230', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v1_funct_2 @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['229'])).
% 0.60/0.86  thf('231', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['169'])).
% 0.60/0.86  thf('232', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('233', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('234', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('235', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (v1_funct_2 @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ (sk_E @ X11 @ X9 @ X10)) @ 
% 0.60/0.86             (u1_struct_0 @ X9) @ (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('236', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_2 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['234', '235'])).
% 0.60/0.86  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('239', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (v1_funct_2 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['236', '237', '238'])).
% 0.60/0.86  thf('240', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_2 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['233', '239'])).
% 0.60/0.86  thf('241', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('242', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (v1_funct_2 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['240', '241'])).
% 0.60/0.86  thf('243', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v1_funct_2 @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['232', '242'])).
% 0.60/0.86  thf('244', plain,
% 0.60/0.86      ((((v1_funct_2 @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['231', '243'])).
% 0.60/0.86  thf('245', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v1_funct_2 @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['244'])).
% 0.60/0.86  thf('246', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['147'])).
% 0.60/0.86  thf('247', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('248', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('249', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('250', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (m1_subset_1 @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ (sk_E @ X11 @ X9 @ X10)) @ 
% 0.60/0.86             (k1_zfmisc_1 @ 
% 0.60/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ 
% 0.60/0.86               (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('251', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (m1_subset_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (k1_zfmisc_1 @ 
% 0.60/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.60/0.86               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['249', '250'])).
% 0.60/0.86  thf('252', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('253', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('254', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (m1_subset_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (k1_zfmisc_1 @ 
% 0.60/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.60/0.86               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['251', '252', '253'])).
% 0.60/0.86  thf('255', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (m1_subset_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (k1_zfmisc_1 @ 
% 0.60/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['248', '254'])).
% 0.60/0.86  thf('256', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('257', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (m1_subset_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (k1_zfmisc_1 @ 
% 0.60/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['255', '256'])).
% 0.60/0.86  thf('258', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (m1_subset_1 @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86            (k1_zfmisc_1 @ 
% 0.60/0.86             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['247', '257'])).
% 0.60/0.86  thf('259', plain,
% 0.60/0.86      ((((m1_subset_1 @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86          (k1_zfmisc_1 @ 
% 0.60/0.86           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['246', '258'])).
% 0.60/0.86  thf('260', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (m1_subset_1 @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86            (k1_zfmisc_1 @ 
% 0.60/0.86             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['259'])).
% 0.60/0.86  thf('261', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ((k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86             = (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86                (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['169'])).
% 0.60/0.86  thf('262', plain,
% 0.60/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('split', [status(esa)], ['28'])).
% 0.60/0.86  thf('263', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('264', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('265', plain,
% 0.60/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X9)
% 0.60/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.60/0.86          | (m1_subset_1 @ 
% 0.60/0.86             (k3_tmap_1 @ X10 @ (sk_D @ X11 @ X9 @ X10) @ 
% 0.60/0.86              (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ (sk_E @ X11 @ X9 @ X10)) @ 
% 0.60/0.86             (k1_zfmisc_1 @ 
% 0.60/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ 
% 0.60/0.86               (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))))
% 0.60/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.60/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.86          | (v2_struct_0 @ X11)
% 0.60/0.86          | ~ (l1_pre_topc @ X10)
% 0.60/0.86          | ~ (v2_pre_topc @ X10)
% 0.60/0.86          | (v2_struct_0 @ X10))),
% 0.60/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.60/0.86  thf('266', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (m1_subset_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (k1_zfmisc_1 @ 
% 0.60/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['264', '265'])).
% 0.60/0.86  thf('267', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('268', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('269', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_A)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.86          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 0.60/0.86          | (m1_subset_1 @ 
% 0.60/0.86             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 0.60/0.86             (k1_zfmisc_1 @ 
% 0.60/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 0.60/0.86          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['266', '267', '268'])).
% 0.60/0.86  thf('270', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (m1_subset_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (k1_zfmisc_1 @ 
% 0.60/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['263', '269'])).
% 0.60/0.86  thf('271', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('272', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.60/0.86        | (m1_subset_1 @ 
% 0.60/0.86           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86           (k1_zfmisc_1 @ 
% 0.60/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('demod', [status(thm)], ['270', '271'])).
% 0.60/0.86  thf('273', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (m1_subset_1 @ 
% 0.60/0.86            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_B @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.60/0.86            (k1_zfmisc_1 @ 
% 0.60/0.86             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup-', [status(thm)], ['262', '272'])).
% 0.60/0.86  thf('274', plain,
% 0.60/0.86      ((((m1_subset_1 @ 
% 0.60/0.86          (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86           (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86          (k1_zfmisc_1 @ 
% 0.60/0.86           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('sup+', [status(thm)], ['261', '273'])).
% 0.60/0.86  thf('275', plain,
% 0.60/0.86      ((((v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (m1_subset_1 @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86             (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86            (k1_zfmisc_1 @ 
% 0.60/0.86             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.60/0.86      inference('simplify', [status(thm)], ['274'])).
% 0.60/0.86  thf('276', plain,
% 0.60/0.86      ((![X15 : $i, X16 : $i]:
% 0.60/0.86          ((v2_struct_0 @ X15)
% 0.60/0.86           | ~ (v2_pre_topc @ X15)
% 0.60/0.86           | ~ (l1_pre_topc @ X15)
% 0.60/0.86           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.86           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.86           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ sk_B @ 
% 0.60/0.86                X15)
% 0.60/0.86           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                (k1_zfmisc_1 @ 
% 0.60/0.86                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))))
% 0.60/0.86           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.60/0.86           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.60/0.86           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ sk_C @ 
% 0.60/0.86                X15)
% 0.60/0.86           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                (k1_zfmisc_1 @ 
% 0.60/0.86                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))))
% 0.60/0.86           | ~ (v1_funct_1 @ X16)
% 0.60/0.86           | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.86                (k1_zfmisc_1 @ 
% 0.60/0.86                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))))
% 0.60/0.86           | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))
% 0.60/0.86           | (v5_pre_topc @ X16 @ sk_A @ X15)))
% 0.60/0.86         <= ((![X15 : $i, X16 : $i]:
% 0.60/0.86                ((v2_struct_0 @ X15)
% 0.60/0.86                 | ~ (v2_pre_topc @ X15)
% 0.60/0.86                 | ~ (l1_pre_topc @ X15)
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      sk_B @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      sk_C @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_1 @ X16)
% 0.60/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                      (u1_struct_0 @ X15))
% 0.60/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.60/0.86      inference('split', [status(esa)], ['46'])).
% 0.60/0.86  thf('277', plain,
% 0.60/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.60/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_zfmisc_1 @ 
% 0.60/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (m1_subset_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              (k1_zfmisc_1 @ 
% 0.60/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | ~ (v5_pre_topc @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_2 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (v1_funct_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.60/0.86         | ~ (v5_pre_topc @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_2 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (v1_funct_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.60/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.60/0.86             (![X15 : $i, X16 : $i]:
% 0.60/0.86                ((v2_struct_0 @ X15)
% 0.60/0.86                 | ~ (v2_pre_topc @ X15)
% 0.60/0.86                 | ~ (l1_pre_topc @ X15)
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      sk_B @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      sk_C @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_1 @ X16)
% 0.60/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                      (u1_struct_0 @ X15))
% 0.60/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.60/0.86      inference('sup-', [status(thm)], ['275', '276'])).
% 0.60/0.86  thf('278', plain,
% 0.60/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.60/0.86         | ~ (v1_funct_2 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (v5_pre_topc @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.60/0.86         | ~ (v1_funct_2 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (v5_pre_topc @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (m1_subset_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              (k1_zfmisc_1 @ 
% 0.60/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_zfmisc_1 @ 
% 0.60/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.60/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.60/0.86             (![X15 : $i, X16 : $i]:
% 0.60/0.86                ((v2_struct_0 @ X15)
% 0.60/0.86                 | ~ (v2_pre_topc @ X15)
% 0.60/0.86                 | ~ (l1_pre_topc @ X15)
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      sk_B @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      sk_C @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_1 @ X16)
% 0.60/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.60/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                        (u1_struct_0 @ X15))))
% 0.60/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                      (u1_struct_0 @ X15))
% 0.60/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.60/0.86      inference('simplify', [status(thm)], ['277'])).
% 0.60/0.86  thf('279', plain,
% 0.60/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | (v2_struct_0 @ sk_A)
% 0.60/0.86         | (v2_struct_0 @ sk_C)
% 0.60/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.60/0.86         | (v2_struct_0 @ sk_B)
% 0.60/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.60/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ sk_A) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86              (k1_zfmisc_1 @ 
% 0.60/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.60/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v5_pre_topc @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_2 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ sk_C) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (v1_funct_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.60/0.86         | ~ (v5_pre_topc @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v1_funct_2 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ sk_B) @ 
% 0.60/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.60/0.86         | ~ (v1_funct_1 @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.60/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.60/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.60/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.60/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.60/0.86             (![X15 : $i, X16 : $i]:
% 0.60/0.86                ((v2_struct_0 @ X15)
% 0.60/0.86                 | ~ (v2_pre_topc @ X15)
% 0.60/0.86                 | ~ (l1_pre_topc @ X15)
% 0.60/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.60/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.60/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      sk_B @ X15)
% 0.60/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.60/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['260', '278'])).
% 0.69/0.86  thf('280', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (v1_funct_2 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.69/0.86              (u1_struct_0 @ sk_B) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.69/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_2 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              (u1_struct_0 @ sk_C) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['279'])).
% 0.69/0.86  thf('281', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              (u1_struct_0 @ sk_C) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.69/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['245', '280'])).
% 0.69/0.86  thf('282', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.69/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_2 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              (u1_struct_0 @ sk_C) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['281'])).
% 0.69/0.86  thf('283', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.69/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['230', '282'])).
% 0.69/0.86  thf('284', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B) @ 
% 0.69/0.86              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['283'])).
% 0.69/0.86  thf('285', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['215', '284'])).
% 0.69/0.86  thf('286', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v5_pre_topc @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) @ 
% 0.69/0.86              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['285'])).
% 0.69/0.86  thf('287', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['200', '286'])).
% 0.69/0.86  thf('288', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (k1_zfmisc_1 @ 
% 0.69/0.86               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['287'])).
% 0.69/0.86  thf('289', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['185', '288'])).
% 0.69/0.86  thf('290', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_B))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['289'])).
% 0.69/0.86  thf('291', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['184', '290'])).
% 0.69/0.86  thf('292', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ 
% 0.69/0.86              (k2_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86               (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['291'])).
% 0.69/0.86  thf('293', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['162', '292'])).
% 0.69/0.86  thf('294', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['293'])).
% 0.69/0.86  thf('295', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['90', '294'])).
% 0.69/0.86  thf('296', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['295'])).
% 0.69/0.86  thf('297', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['78', '296'])).
% 0.69/0.86  thf('298', plain,
% 0.69/0.86      (((~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['297'])).
% 0.69/0.86  thf('299', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['68', '298'])).
% 0.69/0.86  thf('300', plain,
% 0.69/0.86      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['299'])).
% 0.69/0.86  thf('301', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['58', '300'])).
% 0.69/0.86  thf('302', plain,
% 0.69/0.86      ((((v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86          (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['301'])).
% 0.69/0.86  thf('303', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['79', '89'])).
% 0.69/0.86  thf('304', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86            (k1_zfmisc_1 @ 
% 0.69/0.86             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['96', '106'])).
% 0.69/0.86  thf('305', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('306', plain,
% 0.69/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X9)
% 0.69/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.69/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.69/0.86          | ~ (v1_funct_1 @ (sk_E @ X11 @ X9 @ X10))
% 0.69/0.86          | ~ (v1_funct_2 @ (sk_E @ X11 @ X9 @ X10) @ 
% 0.69/0.86               (u1_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)) @ 
% 0.69/0.86               (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))
% 0.69/0.86          | ~ (v5_pre_topc @ (sk_E @ X11 @ X9 @ X10) @ 
% 0.69/0.86               (k1_tsep_1 @ X10 @ X9 @ X11) @ (sk_D @ X11 @ X9 @ X10))
% 0.69/0.86          | ~ (m1_subset_1 @ (sk_E @ X11 @ X9 @ X10) @ 
% 0.69/0.86               (k1_zfmisc_1 @ 
% 0.69/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)) @ 
% 0.69/0.86                 (u1_struct_0 @ (sk_D @ X11 @ X9 @ X10)))))
% 0.69/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.69/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.69/0.86          | (v2_struct_0 @ X11)
% 0.69/0.86          | ~ (l1_pre_topc @ X10)
% 0.69/0.86          | ~ (v2_pre_topc @ X10)
% 0.69/0.86          | (v2_struct_0 @ X10))),
% 0.69/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.69/0.86  thf('307', plain,
% 0.69/0.86      ((~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86           (k1_zfmisc_1 @ 
% 0.69/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86        | (v2_struct_0 @ sk_A)
% 0.69/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.86        | (v2_struct_0 @ sk_C)
% 0.69/0.86        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.69/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86        | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86        | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.69/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86        | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.69/0.86        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.69/0.86        | (v2_struct_0 @ sk_B))),
% 0.69/0.86      inference('sup-', [status(thm)], ['305', '306'])).
% 0.69/0.86  thf('308', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('309', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('310', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('311', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('312', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('313', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('314', plain,
% 0.69/0.86      ((~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86           (k1_zfmisc_1 @ 
% 0.69/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.69/0.86        | (v2_struct_0 @ sk_A)
% 0.69/0.86        | (v2_struct_0 @ sk_C)
% 0.69/0.86        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86        | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86             (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86        | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86        | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.69/0.86        | (v2_struct_0 @ sk_B))),
% 0.69/0.86      inference('demod', [status(thm)],
% 0.69/0.86                ['307', '308', '309', '310', '311', '312', '313'])).
% 0.69/0.86  thf('315', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86              (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['304', '314'])).
% 0.69/0.86  thf('316', plain,
% 0.69/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('split', [status(esa)], ['28'])).
% 0.69/0.86  thf('317', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86              (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('demod', [status(thm)], ['315', '316'])).
% 0.69/0.86  thf('318', plain,
% 0.69/0.86      (((~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ sk_A) @ 
% 0.69/0.86              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['317'])).
% 0.69/0.86  thf('319', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86              (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['303', '318'])).
% 0.69/0.86  thf('320', plain,
% 0.69/0.86      (((~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_A @ 
% 0.69/0.86            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['319'])).
% 0.69/0.86  thf('321', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['302', '320'])).
% 0.69/0.86  thf('322', plain,
% 0.69/0.86      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['321'])).
% 0.69/0.86  thf('323', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['57', '322'])).
% 0.69/0.86  thf('324', plain,
% 0.69/0.86      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['323'])).
% 0.69/0.86  thf('325', plain,
% 0.69/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X9)
% 0.69/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.69/0.86          | ~ (r1_tsep_1 @ X9 @ X11)
% 0.69/0.86          | ~ (v2_struct_0 @ (sk_D @ X11 @ X9 @ X10))
% 0.69/0.86          | (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.69/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.69/0.86          | (v2_struct_0 @ X11)
% 0.69/0.86          | ~ (l1_pre_topc @ X10)
% 0.69/0.86          | ~ (v2_pre_topc @ X10)
% 0.69/0.86          | (v2_struct_0 @ X10))),
% 0.69/0.86      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.69/0.86  thf('326', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | ~ (v2_pre_topc @ sk_A)
% 0.69/0.86         | ~ (l1_pre_topc @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.69/0.86         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      sk_C @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ X16)
% 0.69/0.86                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.86                      (u1_struct_0 @ X15))
% 0.69/0.86                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['324', '325'])).
% 0.69/0.86  thf('327', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('328', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('329', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('330', plain,
% 0.69/0.86      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.69/0.86      inference('split', [status(esa)], ['28'])).
% 0.69/0.86  thf('331', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('332', plain,
% 0.69/0.86      ((((v2_struct_0 @ sk_B)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_A)
% 0.69/0.86         | (v2_struct_0 @ sk_C)
% 0.69/0.86         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.86         | (v2_struct_0 @ sk_B)))
% 0.69/0.86         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.86             (![X15 : $i, X16 : $i]:
% 0.69/0.86                ((v2_struct_0 @ X15)
% 0.69/0.86                 | ~ (v2_pre_topc @ X15)
% 0.69/0.86                 | ~ (l1_pre_topc @ X15)
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      sk_B @ X15)
% 0.69/0.86                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.86                      (k1_zfmisc_1 @ 
% 0.69/0.86                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.86                        (u1_struct_0 @ X15))))
% 0.69/0.86                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.86                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.86                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.86                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      sk_C @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ X16)
% 0.69/0.87                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                      (u1_struct_0 @ X15))
% 0.69/0.87                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.87      inference('demod', [status(thm)],
% 0.69/0.87                ['326', '327', '328', '329', '330', '331'])).
% 0.69/0.87  thf('333', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.87             (![X15 : $i, X16 : $i]:
% 0.69/0.87                ((v2_struct_0 @ X15)
% 0.69/0.87                 | ~ (v2_pre_topc @ X15)
% 0.69/0.87                 | ~ (l1_pre_topc @ X15)
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      sk_B @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      sk_C @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ X16)
% 0.69/0.87                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                      (u1_struct_0 @ X15))
% 0.69/0.87                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.87      inference('simplify', [status(thm)], ['332'])).
% 0.69/0.87  thf('334', plain,
% 0.69/0.87      ((~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.87         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.87      inference('split', [status(esa)], ['6'])).
% 0.69/0.87  thf('335', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.87             (![X15 : $i, X16 : $i]:
% 0.69/0.87                ((v2_struct_0 @ X15)
% 0.69/0.87                 | ~ (v2_pre_topc @ X15)
% 0.69/0.87                 | ~ (l1_pre_topc @ X15)
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      sk_B @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      sk_C @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ X16)
% 0.69/0.87                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                      (u1_struct_0 @ X15))
% 0.69/0.87                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['333', '334'])).
% 0.69/0.87  thf('336', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('337', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.69/0.87         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.87             (![X15 : $i, X16 : $i]:
% 0.69/0.87                ((v2_struct_0 @ X15)
% 0.69/0.87                 | ~ (v2_pre_topc @ X15)
% 0.69/0.87                 | ~ (l1_pre_topc @ X15)
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      sk_B @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      sk_C @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ X16)
% 0.69/0.87                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                      (u1_struct_0 @ X15))
% 0.69/0.87                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.87      inference('clc', [status(thm)], ['335', '336'])).
% 0.69/0.87  thf('338', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('339', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_C))
% 0.69/0.87         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 0.69/0.87             (![X15 : $i, X16 : $i]:
% 0.69/0.87                ((v2_struct_0 @ X15)
% 0.69/0.87                 | ~ (v2_pre_topc @ X15)
% 0.69/0.87                 | ~ (l1_pre_topc @ X15)
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      sk_B @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.87                 | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.87                 | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      sk_C @ X15)
% 0.69/0.87                 | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_1 @ X16)
% 0.69/0.87                 | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.87                      (k1_zfmisc_1 @ 
% 0.69/0.87                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                        (u1_struct_0 @ X15))))
% 0.69/0.87                 | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                      (u1_struct_0 @ X15))
% 0.69/0.87                 | (v5_pre_topc @ X16 @ sk_A @ X15))))),
% 0.69/0.87      inference('clc', [status(thm)], ['337', '338'])).
% 0.69/0.87  thf('340', plain, (~ (v2_struct_0 @ sk_C)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('341', plain,
% 0.69/0.87      (~
% 0.69/0.87       (![X15 : $i, X16 : $i]:
% 0.69/0.87          ((v2_struct_0 @ X15)
% 0.69/0.87           | ~ (v2_pre_topc @ X15)
% 0.69/0.87           | ~ (l1_pre_topc @ X15)
% 0.69/0.87           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B))
% 0.69/0.87           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))
% 0.69/0.87           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ sk_B @ 
% 0.69/0.87                X15)
% 0.69/0.87           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_B) @ 
% 0.69/0.87                (k1_zfmisc_1 @ 
% 0.69/0.87                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X15))))
% 0.69/0.87           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C))
% 0.69/0.87           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))
% 0.69/0.87           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ sk_C @ 
% 0.69/0.87                X15)
% 0.69/0.87           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X15 @ X16 @ sk_C) @ 
% 0.69/0.87                (k1_zfmisc_1 @ 
% 0.69/0.87                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X15))))
% 0.69/0.87           | ~ (v1_funct_1 @ X16)
% 0.69/0.87           | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.87                (k1_zfmisc_1 @ 
% 0.69/0.87                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))))
% 0.69/0.87           | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X15))
% 0.69/0.87           | (v5_pre_topc @ X16 @ sk_A @ X15))) | 
% 0.69/0.87       ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.69/0.87      inference('sup-', [status(thm)], ['339', '340'])).
% 0.69/0.87  thf('342', plain,
% 0.69/0.87      (((l1_pre_topc @ sk_D_1)
% 0.69/0.87        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.69/0.87        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('343', plain,
% 0.69/0.87      (((l1_pre_topc @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 0.69/0.87       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.69/0.87      inference('split', [status(esa)], ['342'])).
% 0.69/0.87  thf('344', plain,
% 0.69/0.87      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B)))
% 0.69/0.87         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))))),
% 0.69/0.87      inference('split', [status(esa)], ['24'])).
% 0.69/0.87  thf('345', plain,
% 0.69/0.87      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C)))
% 0.69/0.87         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))))),
% 0.69/0.87      inference('split', [status(esa)], ['16'])).
% 0.69/0.87  thf('346', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('347', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['342'])).
% 0.69/0.87  thf('348', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['6'])).
% 0.69/0.87  thf('349', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['4'])).
% 0.69/0.87  thf('350', plain,
% 0.69/0.87      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))))),
% 0.69/0.87      inference('split', [status(esa)], ['8'])).
% 0.69/0.87  thf('351', plain,
% 0.69/0.87      (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))))
% 0.69/0.87         <= (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('split', [status(esa)], ['10'])).
% 0.69/0.87  thf('352', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.87         ((v2_struct_0 @ X0)
% 0.69/0.87          | ~ (v2_pre_topc @ X0)
% 0.69/0.87          | ~ (l1_pre_topc @ X0)
% 0.69/0.87          | ~ (m1_pre_topc @ X1 @ X2)
% 0.69/0.87          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.69/0.87              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.69/0.87                 (u1_struct_0 @ X1)))
% 0.69/0.87          | ~ (m1_subset_1 @ X3 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.69/0.87          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v1_funct_1 @ X3)
% 0.69/0.87          | ~ (l1_pre_topc @ X2)
% 0.69/0.87          | ~ (v2_pre_topc @ X2)
% 0.69/0.87          | (v2_struct_0 @ X2))),
% 0.69/0.87      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.69/0.87  thf('353', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_A)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_A)
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                (u1_struct_0 @ sk_D_1))
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_D_1)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['351', '352'])).
% 0.69/0.87  thf('354', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('355', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('356', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                (u1_struct_0 @ sk_D_1))
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_D_1)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('demod', [status(thm)], ['353', '354', '355'])).
% 0.69/0.87  thf('357', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_D_1)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['350', '356'])).
% 0.69/0.87  thf('358', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['349', '357'])).
% 0.69/0.87  thf('359', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_D_1)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['348', '358'])).
% 0.69/0.87  thf('360', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['347', '359'])).
% 0.69/0.87  thf('361', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B)
% 0.69/0.87             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87                sk_E_1 @ (u1_struct_0 @ sk_B)))
% 0.69/0.87         | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['346', '360'])).
% 0.69/0.87  thf('362', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('363', plain,
% 0.69/0.87      (((((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B)
% 0.69/0.87           = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87              sk_E_1 @ (u1_struct_0 @ sk_B)))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('clc', [status(thm)], ['361', '362'])).
% 0.69/0.87  thf('364', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('365', plain,
% 0.69/0.87      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.69/0.87  thf('366', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['342'])).
% 0.69/0.87  thf('367', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['6'])).
% 0.69/0.87  thf('368', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['4'])).
% 0.69/0.87  thf('369', plain,
% 0.69/0.87      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))))),
% 0.69/0.87      inference('split', [status(esa)], ['8'])).
% 0.69/0.87  thf('370', plain,
% 0.69/0.87      (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))))
% 0.69/0.87         <= (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('split', [status(esa)], ['10'])).
% 0.69/0.87  thf('371', plain,
% 0.69/0.87      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.87         ((v2_struct_0 @ X4)
% 0.69/0.87          | ~ (v2_pre_topc @ X4)
% 0.69/0.87          | ~ (l1_pre_topc @ X4)
% 0.69/0.87          | ~ (m1_pre_topc @ X5 @ X6)
% 0.69/0.87          | ~ (m1_pre_topc @ X5 @ X7)
% 0.69/0.87          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 0.69/0.87              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 0.69/0.87                 (u1_struct_0 @ X5)))
% 0.69/0.87          | ~ (m1_subset_1 @ X8 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 0.69/0.87          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 0.69/0.87          | ~ (v1_funct_1 @ X8)
% 0.69/0.87          | ~ (m1_pre_topc @ X7 @ X6)
% 0.69/0.87          | ~ (l1_pre_topc @ X6)
% 0.69/0.87          | ~ (v2_pre_topc @ X6)
% 0.69/0.87          | (v2_struct_0 @ X6))),
% 0.69/0.87      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.69/0.87  thf('372', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          ((v2_struct_0 @ X0)
% 0.69/0.87           | ~ (v2_pre_topc @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ X0)
% 0.69/0.87           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                (u1_struct_0 @ sk_D_1))
% 0.69/0.87           | ((k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X1)))
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_D_1)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['370', '371'])).
% 0.69/0.87  thf('373', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_D_1)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.69/0.87           | ((k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X1)))
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ X0)
% 0.69/0.87           | ~ (v2_pre_topc @ X0)
% 0.69/0.87           | (v2_struct_0 @ X0)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['369', '372'])).
% 0.69/0.87  thf('374', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          ((v2_struct_0 @ X0)
% 0.69/0.87           | ~ (v2_pre_topc @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ X0)
% 0.69/0.87           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.69/0.87           | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87           | ((k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X1)))
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['368', '373'])).
% 0.69/0.87  thf('375', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_D_1)
% 0.69/0.87           | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.69/0.87           | ((k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X1)))
% 0.69/0.87           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ X0)
% 0.69/0.87           | ~ (v2_pre_topc @ X0)
% 0.69/0.87           | (v2_struct_0 @ X0)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['367', '374'])).
% 0.69/0.87  thf('376', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          ((v2_struct_0 @ X0)
% 0.69/0.87           | ~ (v2_pre_topc @ X0)
% 0.69/0.87           | ~ (l1_pre_topc @ X0)
% 0.69/0.87           | ~ (m1_pre_topc @ sk_A @ X0)
% 0.69/0.87           | ((k3_tmap_1 @ X0 @ sk_D_1 @ sk_A @ X1 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X1)))
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.69/0.87           | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['366', '375'])).
% 0.69/0.87  thf('377', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          (~ (l1_pre_topc @ sk_A)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (l1_pre_topc @ sk_A)
% 0.69/0.87           | ~ (v2_pre_topc @ sk_A)
% 0.69/0.87           | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['365', '376'])).
% 0.69/0.87  thf('378', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('379', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('380', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('381', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_D_1)
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('demod', [status(thm)], ['377', '378', '379', '380'])).
% 0.69/0.87  thf('382', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['381'])).
% 0.69/0.87  thf('383', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87                sk_E_1 @ (u1_struct_0 @ sk_B)))
% 0.69/0.87         | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['364', '382'])).
% 0.69/0.87  thf('384', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('385', plain,
% 0.69/0.87      (((((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87           = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87              sk_E_1 @ (u1_struct_0 @ sk_B)))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('clc', [status(thm)], ['383', '384'])).
% 0.69/0.87  thf('386', plain,
% 0.69/0.87      (((((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87           = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup+', [status(thm)], ['363', '385'])).
% 0.69/0.87  thf('387', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['386'])).
% 0.69/0.87  thf('388', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('389', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ X0)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['347', '359'])).
% 0.69/0.87  thf('390', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C)
% 0.69/0.87             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87                sk_E_1 @ (u1_struct_0 @ sk_C)))
% 0.69/0.87         | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['388', '389'])).
% 0.69/0.87  thf('391', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('392', plain,
% 0.69/0.87      (((((k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C)
% 0.69/0.87           = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87              sk_E_1 @ (u1_struct_0 @ sk_C)))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('clc', [status(thm)], ['390', '391'])).
% 0.69/0.87  thf('393', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('394', plain,
% 0.69/0.87      ((![X0 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_A)
% 0.69/0.87           | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ X0 @ sk_E_1)
% 0.69/0.87               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87                  (u1_struct_0 @ sk_D_1) @ sk_E_1 @ (u1_struct_0 @ X0)))
% 0.69/0.87           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.69/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['381'])).
% 0.69/0.87  thf('395', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87             = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87                sk_E_1 @ (u1_struct_0 @ sk_C)))
% 0.69/0.87         | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['393', '394'])).
% 0.69/0.87  thf('396', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('397', plain,
% 0.69/0.87      (((((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87           = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1) @ 
% 0.69/0.87              sk_E_1 @ (u1_struct_0 @ sk_C)))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('clc', [status(thm)], ['395', '396'])).
% 0.69/0.87  thf('398', plain,
% 0.69/0.87      (((((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87           = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup+', [status(thm)], ['392', '397'])).
% 0.69/0.87  thf('399', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['398'])).
% 0.69/0.87  thf('400', plain,
% 0.69/0.87      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ sk_B @ 
% 0.69/0.87         sk_D_1))
% 0.69/0.87         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['20'])).
% 0.69/0.87  thf('401', plain,
% 0.69/0.87      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ sk_C @ 
% 0.69/0.87         sk_D_1))
% 0.69/0.87         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['12'])).
% 0.69/0.87  thf('402', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['386'])).
% 0.69/0.87  thf('403', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['398'])).
% 0.69/0.87  thf('404', plain,
% 0.69/0.87      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))),
% 0.69/0.87      inference('split', [status(esa)], ['22'])).
% 0.69/0.87  thf('405', plain,
% 0.69/0.87      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.69/0.87      inference('split', [status(esa)], ['14'])).
% 0.69/0.87  thf('406', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['386'])).
% 0.69/0.87  thf('407', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['398'])).
% 0.69/0.87  thf('408', plain,
% 0.69/0.87      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 0.69/0.87         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('split', [status(esa)], ['26'])).
% 0.69/0.87  thf('409', plain,
% 0.69/0.87      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 0.69/0.87         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('split', [status(esa)], ['18'])).
% 0.69/0.87  thf('410', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['398'])).
% 0.69/0.87  thf('411', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ((k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1)
% 0.69/0.87             = (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))))
% 0.69/0.87         <= (((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['386'])).
% 0.69/0.87  thf('412', plain,
% 0.69/0.87      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.87      inference('split', [status(esa)], ['28'])).
% 0.69/0.87  thf('413', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('414', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.87         ((v2_struct_0 @ X9)
% 0.69/0.87          | ~ (m1_pre_topc @ X9 @ X10)
% 0.69/0.87          | ~ (r3_tsep_1 @ X10 @ X9 @ X11)
% 0.69/0.87          | ~ (v1_funct_1 @ X12)
% 0.69/0.87          | ~ (v1_funct_2 @ X12 @ 
% 0.69/0.87               (u1_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)) @ 
% 0.69/0.87               (u1_struct_0 @ X13))
% 0.69/0.87          | ~ (m1_subset_1 @ X12 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X10 @ X9 @ X11)) @ 
% 0.69/0.87                 (u1_struct_0 @ X13))))
% 0.69/0.87          | (v5_pre_topc @ X12 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X13)
% 0.69/0.87          | ~ (m1_subset_1 @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ 
% 0.69/0.87                X12) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))))
% 0.69/0.87          | ~ (v5_pre_topc @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ 
% 0.69/0.87                X12) @ 
% 0.69/0.87               X11 @ X13)
% 0.69/0.87          | ~ (v1_funct_2 @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ 
% 0.69/0.87                X12) @ 
% 0.69/0.87               (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.69/0.87          | ~ (v1_funct_1 @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X11 @ 
% 0.69/0.87                X12))
% 0.69/0.87          | ~ (m1_subset_1 @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ X12) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X13))))
% 0.69/0.87          | ~ (v5_pre_topc @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ X12) @ 
% 0.69/0.87               X9 @ X13)
% 0.69/0.87          | ~ (v1_funct_2 @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ X12) @ 
% 0.69/0.87               (u1_struct_0 @ X9) @ (u1_struct_0 @ X13))
% 0.69/0.87          | ~ (v1_funct_1 @ 
% 0.69/0.87               (k3_tmap_1 @ X10 @ X13 @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X9 @ X12))
% 0.69/0.87          | ~ (l1_pre_topc @ X13)
% 0.69/0.87          | ~ (v2_pre_topc @ X13)
% 0.69/0.87          | (v2_struct_0 @ X13)
% 0.69/0.87          | ~ (m1_pre_topc @ X11 @ X10)
% 0.69/0.87          | (v2_struct_0 @ X11)
% 0.69/0.87          | ~ (l1_pre_topc @ X10)
% 0.69/0.87          | ~ (v2_pre_topc @ X10)
% 0.69/0.87          | (v2_struct_0 @ X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [t135_tmap_1])).
% 0.69/0.87  thf('415', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 0.69/0.87             (k1_zfmisc_1 @ 
% 0.69/0.87              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.69/0.87          | (v2_struct_0 @ sk_A)
% 0.69/0.87          | ~ (v2_pre_topc @ sk_A)
% 0.69/0.87          | ~ (l1_pre_topc @ sk_A)
% 0.69/0.87          | (v2_struct_0 @ sk_C)
% 0.69/0.87          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.69/0.87          | (v2_struct_0 @ X0)
% 0.69/0.87          | ~ (v2_pre_topc @ X0)
% 0.69/0.87          | ~ (l1_pre_topc @ X0)
% 0.69/0.87          | ~ (v1_funct_1 @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_B @ X1))
% 0.69/0.87          | ~ (v1_funct_2 @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_B @ X1) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v5_pre_topc @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_B @ X1) @ 
% 0.69/0.87               sk_B @ X0)
% 0.69/0.87          | ~ (m1_subset_1 @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_B @ X1) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))))
% 0.69/0.87          | ~ (v1_funct_1 @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_C @ X1))
% 0.69/0.87          | ~ (v1_funct_2 @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_C @ X1) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v5_pre_topc @ 
% 0.69/0.87               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.69/0.87                sk_C @ X1) @ 
% 0.69/0.87               sk_C @ X0)
% 0.69/0.87          | (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 0.69/0.87          | ~ (m1_subset_1 @ X1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ 
% 0.69/0.87                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.69/0.87                 (u1_struct_0 @ X0))))
% 0.69/0.87          | ~ (v1_funct_2 @ X1 @ 
% 0.69/0.87               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.69/0.87               (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v1_funct_1 @ X1)
% 0.69/0.87          | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.87          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.69/0.87          | (v2_struct_0 @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['413', '414'])).
% 0.69/0.87  thf('416', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('417', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('418', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('419', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('420', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('421', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('422', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('423', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('424', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('425', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('426', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('427', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('428', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('429', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('430', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 0.69/0.87             (k1_zfmisc_1 @ 
% 0.69/0.87              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.69/0.87          | (v2_struct_0 @ sk_A)
% 0.69/0.87          | (v2_struct_0 @ sk_C)
% 0.69/0.87          | (v2_struct_0 @ X0)
% 0.69/0.87          | ~ (v2_pre_topc @ X0)
% 0.69/0.87          | ~ (l1_pre_topc @ X0)
% 0.69/0.87          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1))
% 0.69/0.87          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1) @ 
% 0.69/0.87               sk_B @ X0)
% 0.69/0.87          | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_B @ X1) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))))
% 0.69/0.87          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1))
% 0.69/0.87          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 0.69/0.87               sk_C @ X0)
% 0.69/0.87          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.69/0.87          | ~ (m1_subset_1 @ X1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.69/0.87          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.69/0.87          | ~ (v1_funct_1 @ X1)
% 0.69/0.87          | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 0.69/0.87          | (v2_struct_0 @ sk_B))),
% 0.69/0.87      inference('demod', [status(thm)],
% 0.69/0.87                ['415', '416', '417', '418', '419', '420', '421', '422', 
% 0.69/0.87                 '423', '424', '425', '426', '427', '428', '429'])).
% 0.69/0.87  thf('431', plain,
% 0.69/0.87      ((![X0 : $i, X1 : $i]:
% 0.69/0.87          ((v2_struct_0 @ sk_B)
% 0.69/0.87           | ~ (v1_funct_1 @ X0)
% 0.69/0.87           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X1))
% 0.69/0.87           | ~ (m1_subset_1 @ X0 @ 
% 0.69/0.87                (k1_zfmisc_1 @ 
% 0.69/0.87                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X1))))
% 0.69/0.87           | (v5_pre_topc @ X0 @ sk_A @ X1)
% 0.69/0.87           | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0) @ 
% 0.69/0.87                sk_C @ X1)
% 0.69/0.87           | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0) @ 
% 0.69/0.87                (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X1))
% 0.69/0.87           | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0))
% 0.69/0.87           | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0) @ 
% 0.69/0.87                (k1_zfmisc_1 @ 
% 0.69/0.87                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X1))))
% 0.69/0.87           | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0) @ 
% 0.69/0.87                sk_B @ X1)
% 0.69/0.87           | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0) @ 
% 0.69/0.87                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X1))
% 0.69/0.87           | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_B @ X0))
% 0.69/0.87           | ~ (l1_pre_topc @ X1)
% 0.69/0.87           | ~ (v2_pre_topc @ X1)
% 0.69/0.87           | (v2_struct_0 @ X1)
% 0.69/0.87           | (v2_struct_0 @ sk_C)
% 0.69/0.87           | (v2_struct_0 @ sk_A)
% 0.69/0.87           | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X1 @ sk_A @ sk_C @ X0) @ 
% 0.69/0.87                (k1_zfmisc_1 @ 
% 0.69/0.87                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X1))))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['412', '430'])).
% 0.69/0.87  thf('432', plain,
% 0.69/0.87      (((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87            (k1_zfmisc_1 @ 
% 0.69/0.87             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (m1_subset_1 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v2_pre_topc @ sk_D_1)
% 0.69/0.87         | ~ (l1_pre_topc @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87              (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ sk_E_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['411', '431'])).
% 0.69/0.87  thf('433', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['4'])).
% 0.69/0.87  thf('434', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['342'])).
% 0.69/0.87  thf('435', plain,
% 0.69/0.87      (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))))
% 0.69/0.87         <= (((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))))),
% 0.69/0.87      inference('split', [status(esa)], ['10'])).
% 0.69/0.87  thf('436', plain,
% 0.69/0.87      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))))),
% 0.69/0.87      inference('split', [status(esa)], ['8'])).
% 0.69/0.87  thf('437', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['6'])).
% 0.69/0.87  thf('438', plain,
% 0.69/0.87      (((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87            (k1_zfmisc_1 @ 
% 0.69/0.87             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (m1_subset_1 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('demod', [status(thm)],
% 0.69/0.87                ['432', '433', '434', '435', '436', '437'])).
% 0.69/0.87  thf('439', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | ~ (m1_subset_1 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['438'])).
% 0.69/0.87  thf('440', plain,
% 0.69/0.87      (((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87            (k1_zfmisc_1 @ 
% 0.69/0.87             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['410', '439'])).
% 0.69/0.87  thf('441', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              (k1_zfmisc_1 @ 
% 0.69/0.87               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['440'])).
% 0.69/0.87  thf('442', plain,
% 0.69/0.87      (((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87            (k1_zfmisc_1 @ 
% 0.69/0.87             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['409', '441'])).
% 0.69/0.87  thf('443', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['408', '442'])).
% 0.69/0.87  thf('444', plain,
% 0.69/0.87      (((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['407', '443'])).
% 0.69/0.87  thf('445', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['444'])).
% 0.69/0.87  thf('446', plain,
% 0.69/0.87      (((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['406', '445'])).
% 0.69/0.87  thf('447', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['446'])).
% 0.69/0.87  thf('448', plain,
% 0.69/0.87      (((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['405', '447'])).
% 0.69/0.87  thf('449', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1) @ sk_C @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['404', '448'])).
% 0.69/0.87  thf('450', plain,
% 0.69/0.87      (((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ sk_C @ 
% 0.69/0.87            sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['403', '449'])).
% 0.69/0.87  thf('451', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v5_pre_topc @ 
% 0.69/0.87              (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1) @ sk_B @ 
% 0.69/0.87              sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              sk_C @ sk_D_1)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['450'])).
% 0.69/0.87  thf('452', plain,
% 0.69/0.87      (((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ sk_B @ 
% 0.69/0.87            sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              sk_C @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['402', '451'])).
% 0.69/0.87  thf('453', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87              sk_C @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87              sk_B @ sk_D_1)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['452'])).
% 0.69/0.87  thf('454', plain,
% 0.69/0.87      (((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ sk_B @ 
% 0.69/0.87            sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['401', '453'])).
% 0.69/0.87  thf('455', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_C @ sk_E_1))
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['400', '454'])).
% 0.69/0.87  thf('456', plain,
% 0.69/0.87      (((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['399', '455'])).
% 0.69/0.87  thf('457', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_D_1 @ sk_A @ sk_B @ sk_E_1))
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['456'])).
% 0.69/0.87  thf('458', plain,
% 0.69/0.87      (((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['387', '457'])).
% 0.69/0.87  thf('459', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['458'])).
% 0.69/0.87  thf('460', plain,
% 0.69/0.87      (((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['345', '459'])).
% 0.69/0.87  thf('461', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B)
% 0.69/0.87         | (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_D_1)))
% 0.69/0.87         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['344', '460'])).
% 0.69/0.87  thf('462', plain,
% 0.69/0.87      ((~ (v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1))
% 0.69/0.87         <= (~ ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['2'])).
% 0.69/0.87  thf('463', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_C)
% 0.69/0.87         | (v2_struct_0 @ sk_B)))
% 0.69/0.87         <= (~ ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)) & 
% 0.69/0.87             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['461', '462'])).
% 0.69/0.87  thf('464', plain,
% 0.69/0.87      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('465', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 0.69/0.87             ~ ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)) & 
% 0.69/0.87             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['463', '464'])).
% 0.69/0.87  thf('466', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('467', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.69/0.87         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 0.69/0.87             ~ ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)) & 
% 0.69/0.87             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('clc', [status(thm)], ['465', '466'])).
% 0.69/0.87  thf('468', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('469', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_C))
% 0.69/0.87         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 0.69/0.87             ~ ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)) & 
% 0.69/0.87             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 0.69/0.87             ((v1_funct_1 @ sk_E_1)) & 
% 0.69/0.87             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.87               (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               sk_C @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) & 
% 0.69/0.87             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (k1_zfmisc_1 @ 
% 0.69/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 0.69/0.87             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               sk_B @ sk_D_1)) & 
% 0.69/0.87             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) & 
% 0.69/0.87             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) & 
% 0.69/0.87             ((l1_pre_topc @ sk_D_1)) & 
% 0.69/0.87             ((v2_pre_topc @ sk_D_1)))),
% 0.69/0.87      inference('clc', [status(thm)], ['467', '468'])).
% 0.69/0.87  thf('470', plain, (~ (v2_struct_0 @ sk_C)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('471', plain,
% 0.69/0.87      (~ ((l1_pre_topc @ sk_D_1)) | 
% 0.69/0.87       ~
% 0.69/0.87       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 0.69/0.87       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 0.69/0.87       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B))) | 
% 0.69/0.87       ~
% 0.69/0.87       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 0.69/0.87       ~
% 0.69/0.87       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ sk_B @ 
% 0.69/0.87         sk_D_1)) | 
% 0.69/0.87       ~
% 0.69/0.87       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_B) @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 0.69/0.87       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C))) | 
% 0.69/0.87       ~
% 0.69/0.87       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ 
% 0.69/0.87         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 0.69/0.87       ~
% 0.69/0.87       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_D_1 @ sk_E_1 @ sk_C) @ sk_C @ 
% 0.69/0.87         sk_D_1)) | 
% 0.69/0.87       ~
% 0.69/0.87       ((m1_subset_1 @ sk_E_1 @ 
% 0.69/0.87         (k1_zfmisc_1 @ 
% 0.69/0.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))))) | 
% 0.69/0.87       ~
% 0.69/0.87       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_D_1))) | 
% 0.69/0.87       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 0.69/0.87       ((v5_pre_topc @ sk_E_1 @ sk_A @ sk_D_1)) | ((v2_struct_0 @ sk_D_1))),
% 0.69/0.87      inference('sup-', [status(thm)], ['469', '470'])).
% 0.69/0.87  thf('472', plain, ($false),
% 0.69/0.87      inference('sat_resolution*', [status(thm)],
% 0.69/0.87                ['1', '3', '5', '7', '9', '11', '13', '15', '17', '19', '21', 
% 0.69/0.87                 '23', '25', '27', '44', '45', '47', '341', '343', '471'])).
% 0.69/0.87  
% 0.69/0.87  % SZS output end Refutation
% 0.69/0.87  
% 0.69/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
