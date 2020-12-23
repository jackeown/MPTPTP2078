%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BNdl6M6Yvx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:06 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  506 (1432 expanded)
%              Number of leaves         :   23 ( 393 expanded)
%              Depth                    :   19
%              Number of atoms          : 18449 (144698 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   30 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t131_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( v1_tsep_1 @ E @ A )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) )
                          & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( k1_tsep_1 @ A @ D @ E ) @ B )
                          & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                      <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                          & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                          & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                          & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                          & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                          & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_tsep_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( v1_tsep_1 @ E @ A )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( k1_tsep_1 @ A @ D @ E ) @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_tmap_1])).

thf('0',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('29',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t129_tmap_1,axiom,(
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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40','41','42','43','44'])).

thf('46',plain,(
    v1_tsep_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_tsep_1 @ sk_D @ sk_A ),
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

thf('48',plain,(
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

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['45','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','60'])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','61'])).

thf('63',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('75',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85','86','87','88'])).

thf('90',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['76','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','93'])).

thf('95',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('106',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('107',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115','116','117','118','119'])).

thf('121',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['107','122'])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','123'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','124'])).

thf('126',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('137',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('138',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146','147','148','149','150'])).

thf('152',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','153'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','154'])).

thf('156',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','155'])).

thf('157',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('168',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('169',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('170',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176','177','178','179','180','181'])).

thf('183',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','184'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['168','185'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['167','186'])).

thf('188',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('199',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('200',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('201',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('202',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207','208','209','210','211','212','213'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['201','214'])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['200','215'])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['199','216'])).

thf('218',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['198','217'])).

thf('219',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('230',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('232',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['232'])).

thf('234',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('235',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('236',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('237',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['16'])).

thf('238',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('239',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('240',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['242','243','244','245','246','247','248','249','250'])).

thf('252',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['239','251'])).

thf('253',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['238','252'])).

thf('254',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['237','253'])).

thf('255',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['236','254'])).

thf('256',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('257',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['255','256','257'])).

thf('259',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['235','258'])).

thf('260',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['234','259'])).

thf('261',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['233','260'])).

thf('262',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('263',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('273',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['273'])).

thf('275',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['275'])).

thf('277',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['277'])).

thf('279',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['279'])).

thf('281',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['281'])).

thf('283',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['232'])).

thf('284',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('285',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('286',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('287',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['16'])).

thf('288',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('289',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('290',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('291',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('292',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['292','293','294','295','296','297','298','299','300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['289','301'])).

thf('303',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['288','302'])).

thf('304',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['287','303'])).

thf('305',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['286','304'])).

thf('306',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('307',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['305','306','307'])).

thf('309',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['285','308'])).

thf('310',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['284','309'])).

thf('311',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['283','310'])).

thf('312',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('313',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['315','316'])).

thf('318',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['317','318'])).

thf('320',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['319','320'])).

thf('322',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['232'])).

thf('323',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('325',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['325'])).

thf('327',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('328',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('329',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('330',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('331',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('332',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['330','331'])).

thf('333',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['332','333','334','335','336','337','338','339','340','341'])).

thf('343',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['329','342'])).

thf('344',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['328','343'])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['327','344'])).

thf('346',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('347',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('348',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['63'])).

thf('349',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['349','350'])).

thf('352',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['351','352'])).

thf('354',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['353','354'])).

thf('356',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['355','356'])).

thf('358',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('359',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['359'])).

thf('361',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['361'])).

thf('363',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['363'])).

thf('365',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['365'])).

thf('367',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['367'])).

thf('369',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['369'])).

thf('371',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['232'])).

thf('372',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('373',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('374',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('375',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['16'])).

thf('376',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('377',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('378',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('379',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('380',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['378','379'])).

thf('381',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['380','381','382','383','384','385','386','387','388'])).

thf('390',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['377','389'])).

thf('391',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['376','390'])).

thf('392',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['375','391'])).

thf('393',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['374','392'])).

thf('394',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('395',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['393','394','395'])).

thf('397',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['373','396'])).

thf('398',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['372','397'])).

thf('399',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['371','398'])).

thf('400',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('401',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['399','400'])).

thf('402',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['401','402'])).

thf('404',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['403','404'])).

thf('406',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['405','406'])).

thf('408',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('409',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['232'])).

thf('411',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('412',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('413',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['230'])).

thf('414',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['16'])).

thf('415',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('416',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('417',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('418',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ X4 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('419',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['419','420','421','422','423','424','425','426','427'])).

thf('429',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['416','428'])).

thf('430',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['415','429'])).

thf('431',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
        | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['414','430'])).

thf('432',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['413','431'])).

thf('433',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('434',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['432','433','434'])).

thf('436',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['412','435'])).

thf('437',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['411','436'])).

thf('438',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['410','437'])).

thf('439',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('440',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['438','439'])).

thf('441',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('442',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['440','441'])).

thf('443',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('445',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('446',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['444','445'])).

thf('447',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('448',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['446','447'])).

thf('449',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('450',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['449'])).

thf('451',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('452',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('453',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('454',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('455',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('456',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['454','455'])).

thf('457',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('458',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('459',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('460',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['56','57'])).

thf('461',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('462',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('463',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('464',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('465',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('466',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('467',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['456','457','458','459','460','461','462','463','464','465','466'])).

thf('468',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['453','467'])).

thf('469',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['452','468'])).

thf('470',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['451','469'])).

thf('471',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('472',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['470','471'])).

thf('473',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('474',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['472','473'])).

thf('475',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['474','475'])).

thf('477',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('478',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['476','477'])).

thf('479',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('480',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['478','479'])).

thf('481',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','13','15','17','19','21','23','25','27','73','104','135','166','197','228','229','231','271','272','274','276','278','280','282','321','322','324','326','357','358','360','362','364','366','368','370','409','448','450','480'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BNdl6M6Yvx
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1022 iterations in 0.768s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 1.06/1.25  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.06/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.06/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.25  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.25  thf(sk_E_type, type, sk_E: $i).
% 1.06/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.25  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.06/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.06/1.25  thf(t131_tmap_1, conjecture,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25             ( l1_pre_topc @ B ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.25                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                 ( m1_subset_1 @
% 1.06/1.25                   C @ 
% 1.06/1.25                   ( k1_zfmisc_1 @
% 1.06/1.25                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25               ( ![D:$i]:
% 1.06/1.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 1.06/1.25                     ( m1_pre_topc @ D @ A ) ) =>
% 1.06/1.25                   ( ![E:$i]:
% 1.06/1.25                     ( ( ( ~( v2_struct_0 @ E ) ) & ( v1_tsep_1 @ E @ A ) & 
% 1.06/1.25                         ( m1_pre_topc @ E @ A ) ) =>
% 1.06/1.25                       ( ( ( v1_funct_1 @
% 1.06/1.25                             ( k2_tmap_1 @
% 1.06/1.25                               A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) ) & 
% 1.06/1.25                           ( v1_funct_2 @
% 1.06/1.25                             ( k2_tmap_1 @
% 1.06/1.25                               A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                             ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                             ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                           ( v5_pre_topc @
% 1.06/1.25                             ( k2_tmap_1 @
% 1.06/1.25                               A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                             ( k1_tsep_1 @ A @ D @ E ) @ B ) & 
% 1.06/1.25                           ( m1_subset_1 @
% 1.06/1.25                             ( k2_tmap_1 @
% 1.06/1.25                               A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                             ( k1_zfmisc_1 @
% 1.06/1.25                               ( k2_zfmisc_1 @
% 1.06/1.25                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                                 ( u1_struct_0 @ B ) ) ) ) ) <=>
% 1.06/1.25                         ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.06/1.25                           ( v1_funct_2 @
% 1.06/1.25                             ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.25                             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                           ( v5_pre_topc @
% 1.06/1.25                             ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 1.06/1.25                           ( m1_subset_1 @
% 1.06/1.25                             ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.25                             ( k1_zfmisc_1 @
% 1.06/1.25                               ( k2_zfmisc_1 @
% 1.06/1.25                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.06/1.25                           ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 1.06/1.25                           ( v1_funct_2 @
% 1.06/1.25                             ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 1.06/1.25                             ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                           ( v5_pre_topc @
% 1.06/1.25                             ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 1.06/1.25                           ( m1_subset_1 @
% 1.06/1.25                             ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 1.06/1.25                             ( k1_zfmisc_1 @
% 1.06/1.25                               ( k2_zfmisc_1 @
% 1.06/1.25                                 ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i]:
% 1.06/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.25            ( l1_pre_topc @ A ) ) =>
% 1.06/1.25          ( ![B:$i]:
% 1.06/1.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25                ( l1_pre_topc @ B ) ) =>
% 1.06/1.25              ( ![C:$i]:
% 1.06/1.25                ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.25                    ( v1_funct_2 @
% 1.06/1.25                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                    ( m1_subset_1 @
% 1.06/1.25                      C @ 
% 1.06/1.25                      ( k1_zfmisc_1 @
% 1.06/1.25                        ( k2_zfmisc_1 @
% 1.06/1.25                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                  ( ![D:$i]:
% 1.06/1.25                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 1.06/1.25                        ( m1_pre_topc @ D @ A ) ) =>
% 1.06/1.25                      ( ![E:$i]:
% 1.06/1.25                        ( ( ( ~( v2_struct_0 @ E ) ) & ( v1_tsep_1 @ E @ A ) & 
% 1.06/1.25                            ( m1_pre_topc @ E @ A ) ) =>
% 1.06/1.25                          ( ( ( v1_funct_1 @
% 1.06/1.25                                ( k2_tmap_1 @
% 1.06/1.25                                  A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) ) & 
% 1.06/1.25                              ( v1_funct_2 @
% 1.06/1.25                                ( k2_tmap_1 @
% 1.06/1.25                                  A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                                ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                                ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                              ( v5_pre_topc @
% 1.06/1.25                                ( k2_tmap_1 @
% 1.06/1.25                                  A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                                ( k1_tsep_1 @ A @ D @ E ) @ B ) & 
% 1.06/1.25                              ( m1_subset_1 @
% 1.06/1.25                                ( k2_tmap_1 @
% 1.06/1.25                                  A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                                ( k1_zfmisc_1 @
% 1.06/1.25                                  ( k2_zfmisc_1 @
% 1.06/1.25                                    ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 1.06/1.25                                    ( u1_struct_0 @ B ) ) ) ) ) <=>
% 1.06/1.25                            ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.06/1.25                              ( v1_funct_2 @
% 1.06/1.25                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.25                                ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                              ( v5_pre_topc @
% 1.06/1.25                                ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 1.06/1.25                              ( m1_subset_1 @
% 1.06/1.25                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.25                                ( k1_zfmisc_1 @
% 1.06/1.25                                  ( k2_zfmisc_1 @
% 1.06/1.25                                    ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.06/1.25                              ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 1.06/1.25                              ( v1_funct_2 @
% 1.06/1.25                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 1.06/1.25                                ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                              ( v5_pre_topc @
% 1.06/1.25                                ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 1.06/1.25                              ( m1_subset_1 @
% 1.06/1.25                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 1.06/1.25                                ( k1_zfmisc_1 @
% 1.06/1.25                                  ( k2_zfmisc_1 @
% 1.06/1.25                                    ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t131_tmap_1])).
% 1.06/1.25  thf('0', plain,
% 1.06/1.25      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | (v5_pre_topc @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('1', plain,
% 1.06/1.25      (((v5_pre_topc @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.25       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['0'])).
% 1.06/1.25  thf('2', plain,
% 1.06/1.25      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.25       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('4', plain,
% 1.06/1.25      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('5', plain,
% 1.06/1.25      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.25       ((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['4'])).
% 1.06/1.25  thf('6', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('7', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.25       ((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['6'])).
% 1.06/1.25  thf('8', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.25       ((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['8'])).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.25       ((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['10'])).
% 1.06/1.25  thf('12', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('13', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.25       ((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['12'])).
% 1.06/1.25  thf('14', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.25        | (m1_subset_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_zfmisc_1 @ 
% 1.06/1.25            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25             (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('15', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.25       ((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))),
% 1.06/1.25      inference('split', [status(esa)], ['14'])).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.25        | (v1_funct_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.25       ((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('split', [status(esa)], ['16'])).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (v1_funct_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.25       ((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('split', [status(esa)], ['18'])).
% 1.06/1.25  thf('20', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.25        | (v1_funct_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('21', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.25       ((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('split', [status(esa)], ['20'])).
% 1.06/1.25  thf('22', plain,
% 1.06/1.25      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25        | (v1_funct_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.25       ((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('split', [status(esa)], ['22'])).
% 1.06/1.25  thf('24', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.25        | (v1_funct_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('25', plain,
% 1.06/1.25      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.25       ((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('split', [status(esa)], ['24'])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.25        | (v1_funct_1 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('27', plain,
% 1.06/1.25      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.25       ((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.25      inference('split', [status(esa)], ['26'])).
% 1.06/1.25  thf('28', plain,
% 1.06/1.25      (((v1_funct_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.25         <= (((v1_funct_1 @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.25                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.25      inference('split', [status(esa)], ['16'])).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.25        | (v5_pre_topc @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (((v5_pre_topc @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.25         <= (((v5_pre_topc @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.25                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.25      inference('split', [status(esa)], ['29'])).
% 1.06/1.25  thf('31', plain,
% 1.06/1.25      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.25        | (v1_funct_2 @ 
% 1.06/1.25           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('32', plain,
% 1.06/1.25      (((v1_funct_2 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (u1_struct_0 @ sk_B)))
% 1.06/1.25         <= (((v1_funct_2 @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.25                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25               (u1_struct_0 @ sk_B))))),
% 1.06/1.25      inference('split', [status(esa)], ['31'])).
% 1.06/1.25  thf('33', plain,
% 1.06/1.25      (((m1_subset_1 @ 
% 1.06/1.25         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ 
% 1.06/1.25          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25           (u1_struct_0 @ sk_B)))))
% 1.06/1.25         <= (((m1_subset_1 @ 
% 1.06/1.25               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.25                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ 
% 1.06/1.25                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.25                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.25      inference('split', [status(esa)], ['4'])).
% 1.06/1.25  thf(t129_tmap_1, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.25             ( l1_pre_topc @ B ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.25               ( ![D:$i]:
% 1.06/1.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.06/1.25                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 1.06/1.25                     ( ![E:$i]:
% 1.06/1.25                       ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.25                           ( v1_funct_2 @
% 1.06/1.25                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                           ( m1_subset_1 @
% 1.06/1.25                             E @ 
% 1.06/1.25                             ( k1_zfmisc_1 @
% 1.06/1.25                               ( k2_zfmisc_1 @
% 1.06/1.25                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.25                         ( ( ( v1_funct_1 @
% 1.06/1.25                               ( k2_tmap_1 @
% 1.06/1.25                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 1.06/1.25                             ( v1_funct_2 @
% 1.06/1.25                               ( k2_tmap_1 @
% 1.06/1.25                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.06/1.25                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.06/1.25                               ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                             ( v5_pre_topc @
% 1.06/1.25                               ( k2_tmap_1 @
% 1.06/1.25                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.06/1.25                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 1.06/1.25                             ( m1_subset_1 @
% 1.06/1.25                               ( k2_tmap_1 @
% 1.06/1.25                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.06/1.25                               ( k1_zfmisc_1 @
% 1.06/1.25                                 ( k2_zfmisc_1 @
% 1.06/1.25                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.06/1.25                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 1.06/1.25                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 1.06/1.25                             ( v1_funct_2 @
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 1.06/1.25                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                             ( v5_pre_topc @
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 1.06/1.25                             ( m1_subset_1 @
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 1.06/1.25                               ( k1_zfmisc_1 @
% 1.06/1.25                                 ( k2_zfmisc_1 @
% 1.06/1.25                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.06/1.25                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 1.06/1.25                             ( v1_funct_2 @
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 1.06/1.25                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.25                             ( v5_pre_topc @
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 1.06/1.25                             ( m1_subset_1 @
% 1.06/1.25                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 1.06/1.25                               ( k1_zfmisc_1 @
% 1.06/1.25                                 ( k2_zfmisc_1 @
% 1.06/1.25                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.25         ((v2_struct_0 @ X0)
% 1.06/1.25          | ~ (v2_pre_topc @ X0)
% 1.06/1.25          | ~ (l1_pre_topc @ X0)
% 1.06/1.25          | (v2_struct_0 @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.25          | ~ (v1_funct_1 @ 
% 1.06/1.25               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.25          | ~ (v1_funct_2 @ 
% 1.06/1.25               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.25               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.25          | ~ (v5_pre_topc @ 
% 1.06/1.25               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.25               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.25          | ~ (m1_subset_1 @ 
% 1.06/1.25               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.25                 (u1_struct_0 @ X0))))
% 1.06/1.25          | (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.25             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.06/1.25          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.25               (k1_zfmisc_1 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.25          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.25          | ~ (v1_funct_1 @ X3)
% 1.06/1.25          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.25          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.25          | (v2_struct_0 @ X4)
% 1.06/1.25          | ~ (l1_pre_topc @ X2)
% 1.06/1.25          | ~ (v2_pre_topc @ X2)
% 1.06/1.25          | (v2_struct_0 @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.25  thf('35', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A)
% 1.06/1.25         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.25         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25         | (v2_struct_0 @ sk_D)
% 1.06/1.25         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.25         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.25         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.25         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.25         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.25              (k1_zfmisc_1 @ 
% 1.06/1.25               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.25         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.25            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.25         | ~ (v5_pre_topc @ 
% 1.06/1.25              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.25               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.26  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('40', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('41', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('42', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('44', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('45', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['35', '36', '37', '38', '39', '40', '41', '42', '43', '44'])).
% 1.06/1.26  thf('46', plain, ((v1_tsep_1 @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('47', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(t88_tsep_1, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.26       ( ![B:$i]:
% 1.06/1.26         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.26           ( ![C:$i]:
% 1.06/1.26             ( ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.26               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.06/1.26  thf('48', plain,
% 1.06/1.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.06/1.26         (~ (v1_tsep_1 @ X5 @ X6)
% 1.06/1.26          | ~ (m1_pre_topc @ X5 @ X6)
% 1.06/1.26          | (r4_tsep_1 @ X6 @ X5 @ X7)
% 1.06/1.26          | ~ (m1_pre_topc @ X7 @ X6)
% 1.06/1.26          | ~ (v1_tsep_1 @ X7 @ X6)
% 1.06/1.26          | ~ (l1_pre_topc @ X6)
% 1.06/1.26          | ~ (v2_pre_topc @ X6)
% 1.06/1.26          | (v2_struct_0 @ X6))),
% 1.06/1.26      inference('cnf', [status(esa)], [t88_tsep_1])).
% 1.06/1.26  thf('49', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((v2_struct_0 @ sk_A)
% 1.06/1.26          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 1.06/1.26          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26          | (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.26          | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.26  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('52', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('53', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((v2_struct_0 @ sk_A)
% 1.06/1.26          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 1.06/1.26          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26          | (r4_tsep_1 @ sk_A @ sk_D @ X0))),
% 1.06/1.26      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 1.06/1.26  thf('54', plain,
% 1.06/1.26      (((r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26        | (v2_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['46', '53'])).
% 1.06/1.26  thf('55', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('56', plain, (((r4_tsep_1 @ sk_A @ sk_D @ sk_E) | (v2_struct_0 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.06/1.26  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('58', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('59', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)], ['45', '58'])).
% 1.06/1.26  thf('60', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['32', '59'])).
% 1.06/1.26  thf('61', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['30', '60'])).
% 1.06/1.26  thf('62', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['28', '61'])).
% 1.06/1.26  thf('63', plain,
% 1.06/1.26      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26           (k1_zfmisc_1 @ 
% 1.06/1.26            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26             sk_B)
% 1.06/1.26        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.26        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26             (k1_zfmisc_1 @ 
% 1.06/1.26              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26             sk_B)
% 1.06/1.26        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26        | ~ (m1_subset_1 @ 
% 1.06/1.26             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26             (k1_zfmisc_1 @ 
% 1.06/1.26              (k2_zfmisc_1 @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))))
% 1.06/1.26        | ~ (v5_pre_topc @ 
% 1.06/1.26             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26             (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26        | ~ (v1_funct_2 @ 
% 1.06/1.26             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26             (u1_struct_0 @ sk_B))
% 1.06/1.26        | ~ (v1_funct_1 @ 
% 1.06/1.26             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('64', plain,
% 1.06/1.26      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('65', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['62', '64'])).
% 1.06/1.26  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('67', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['65', '66'])).
% 1.06/1.26  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('69', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['67', '68'])).
% 1.06/1.26  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('71', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['69', '70'])).
% 1.06/1.26  thf('72', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('73', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['71', '72'])).
% 1.06/1.26  thf('74', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.26      inference('split', [status(esa)], ['16'])).
% 1.06/1.26  thf('75', plain,
% 1.06/1.26      (((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['29'])).
% 1.06/1.26  thf('76', plain,
% 1.06/1.26      (((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['31'])).
% 1.06/1.26  thf('77', plain,
% 1.06/1.26      (((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['4'])).
% 1.06/1.26  thf('78', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.26         ((v2_struct_0 @ X0)
% 1.06/1.26          | ~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v2_struct_0 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.26          | ~ (v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.26          | ~ (v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26                 (u1_struct_0 @ X0))))
% 1.06/1.26          | (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ X1 @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v1_funct_1 @ X3)
% 1.06/1.26          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.26          | (v2_struct_0 @ X4)
% 1.06/1.26          | ~ (l1_pre_topc @ X2)
% 1.06/1.26          | ~ (v2_pre_topc @ X2)
% 1.06/1.26          | (v2_struct_0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.26  thf('79', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.26         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.26              (k1_zfmisc_1 @ 
% 1.06/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['77', '78'])).
% 1.06/1.26  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('82', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('84', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('85', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('86', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('88', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('89', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['79', '80', '81', '82', '83', '84', '85', '86', '87', '88'])).
% 1.06/1.26  thf('90', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('91', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)], ['89', '90'])).
% 1.06/1.26  thf('92', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['76', '91'])).
% 1.06/1.26  thf('93', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['75', '92'])).
% 1.06/1.26  thf('94', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['74', '93'])).
% 1.06/1.26  thf('95', plain,
% 1.06/1.26      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('96', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['94', '95'])).
% 1.06/1.26  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('98', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['96', '97'])).
% 1.06/1.26  thf('99', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('100', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['98', '99'])).
% 1.06/1.26  thf('101', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('102', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['100', '101'])).
% 1.06/1.26  thf('103', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('104', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['102', '103'])).
% 1.06/1.26  thf('105', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.26      inference('split', [status(esa)], ['16'])).
% 1.06/1.26  thf('106', plain,
% 1.06/1.26      (((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['29'])).
% 1.06/1.26  thf('107', plain,
% 1.06/1.26      (((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['31'])).
% 1.06/1.26  thf('108', plain,
% 1.06/1.26      (((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['4'])).
% 1.06/1.26  thf('109', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.26         ((v2_struct_0 @ X0)
% 1.06/1.26          | ~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v2_struct_0 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.26          | ~ (v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.26          | ~ (v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26                 (u1_struct_0 @ X0))))
% 1.06/1.26          | (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.26             (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v1_funct_1 @ X3)
% 1.06/1.26          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.26          | (v2_struct_0 @ X4)
% 1.06/1.26          | ~ (l1_pre_topc @ X2)
% 1.06/1.26          | ~ (v2_pre_topc @ X2)
% 1.06/1.26          | (v2_struct_0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.26  thf('110', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.26         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.26              (k1_zfmisc_1 @ 
% 1.06/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['108', '109'])).
% 1.06/1.26  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('113', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('115', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('116', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('117', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('119', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('120', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['110', '111', '112', '113', '114', '115', '116', '117', 
% 1.06/1.26                 '118', '119'])).
% 1.06/1.26  thf('121', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('122', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)], ['120', '121'])).
% 1.06/1.26  thf('123', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['107', '122'])).
% 1.06/1.26  thf('124', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['106', '123'])).
% 1.06/1.26  thf('125', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['105', '124'])).
% 1.06/1.26  thf('126', plain,
% 1.06/1.26      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('127', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['125', '126'])).
% 1.06/1.26  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('129', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['127', '128'])).
% 1.06/1.26  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('131', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['129', '130'])).
% 1.06/1.26  thf('132', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('133', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['131', '132'])).
% 1.06/1.26  thf('134', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('135', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['133', '134'])).
% 1.06/1.26  thf('136', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.26      inference('split', [status(esa)], ['16'])).
% 1.06/1.26  thf('137', plain,
% 1.06/1.26      (((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['29'])).
% 1.06/1.26  thf('138', plain,
% 1.06/1.26      (((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['31'])).
% 1.06/1.26  thf('139', plain,
% 1.06/1.26      (((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['4'])).
% 1.06/1.26  thf('140', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.26         ((v2_struct_0 @ X0)
% 1.06/1.26          | ~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v2_struct_0 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.26          | ~ (v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.26          | ~ (v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26                 (u1_struct_0 @ X0))))
% 1.06/1.26          | (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ X4 @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v1_funct_1 @ X3)
% 1.06/1.26          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.26          | (v2_struct_0 @ X4)
% 1.06/1.26          | ~ (l1_pre_topc @ X2)
% 1.06/1.26          | ~ (v2_pre_topc @ X2)
% 1.06/1.26          | (v2_struct_0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.26  thf('141', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.26         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.26              (k1_zfmisc_1 @ 
% 1.06/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['139', '140'])).
% 1.06/1.26  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('144', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('146', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('147', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('148', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('149', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('151', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['141', '142', '143', '144', '145', '146', '147', '148', 
% 1.06/1.26                 '149', '150'])).
% 1.06/1.26  thf('152', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('153', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)], ['151', '152'])).
% 1.06/1.26  thf('154', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['138', '153'])).
% 1.06/1.26  thf('155', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['137', '154'])).
% 1.06/1.26  thf('156', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['136', '155'])).
% 1.06/1.26  thf('157', plain,
% 1.06/1.26      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('158', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['156', '157'])).
% 1.06/1.26  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('160', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['158', '159'])).
% 1.06/1.26  thf('161', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('162', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['160', '161'])).
% 1.06/1.26  thf('163', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('164', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['162', '163'])).
% 1.06/1.26  thf('165', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('166', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['164', '165'])).
% 1.06/1.26  thf('167', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.26      inference('split', [status(esa)], ['16'])).
% 1.06/1.26  thf('168', plain,
% 1.06/1.26      (((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['29'])).
% 1.06/1.26  thf('169', plain,
% 1.06/1.26      (((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['31'])).
% 1.06/1.26  thf('170', plain,
% 1.06/1.26      (((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['4'])).
% 1.06/1.26  thf('171', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.26         ((v2_struct_0 @ X0)
% 1.06/1.26          | ~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v2_struct_0 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.26          | ~ (v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.26          | ~ (v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26                 (u1_struct_0 @ X0))))
% 1.06/1.26          | (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.26             (k1_zfmisc_1 @ 
% 1.06/1.26              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v1_funct_1 @ X3)
% 1.06/1.26          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.26          | (v2_struct_0 @ X4)
% 1.06/1.26          | ~ (l1_pre_topc @ X2)
% 1.06/1.26          | ~ (v2_pre_topc @ X2)
% 1.06/1.26          | (v2_struct_0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.26  thf('172', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.26         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.26              (k1_zfmisc_1 @ 
% 1.06/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (k1_zfmisc_1 @ 
% 1.06/1.26             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['170', '171'])).
% 1.06/1.26  thf('173', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('175', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('177', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('178', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('179', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('180', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('181', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('182', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (k1_zfmisc_1 @ 
% 1.06/1.26             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['172', '173', '174', '175', '176', '177', '178', '179', 
% 1.06/1.26                 '180', '181'])).
% 1.06/1.26  thf('183', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('184', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (k1_zfmisc_1 @ 
% 1.06/1.26             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)], ['182', '183'])).
% 1.06/1.26  thf('185', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (k1_zfmisc_1 @ 
% 1.06/1.26             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['169', '184'])).
% 1.06/1.26  thf('186', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (k1_zfmisc_1 @ 
% 1.06/1.26             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['168', '185'])).
% 1.06/1.26  thf('187', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26            (k1_zfmisc_1 @ 
% 1.06/1.26             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['167', '186'])).
% 1.06/1.26  thf('188', plain,
% 1.06/1.26      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26           (k1_zfmisc_1 @ 
% 1.06/1.26            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (~
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('189', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['187', '188'])).
% 1.06/1.26  thf('190', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('191', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['189', '190'])).
% 1.06/1.26  thf('192', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('193', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['191', '192'])).
% 1.06/1.26  thf('194', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('195', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['193', '194'])).
% 1.06/1.26  thf('196', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('197', plain,
% 1.06/1.26      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['195', '196'])).
% 1.06/1.26  thf('198', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('199', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.26      inference('split', [status(esa)], ['16'])).
% 1.06/1.26  thf('200', plain,
% 1.06/1.26      (((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['29'])).
% 1.06/1.26  thf('201', plain,
% 1.06/1.26      (((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['31'])).
% 1.06/1.26  thf('202', plain,
% 1.06/1.26      (((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['4'])).
% 1.06/1.26  thf('203', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.26         ((v2_struct_0 @ X0)
% 1.06/1.26          | ~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v2_struct_0 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.26          | ~ (v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.26          | ~ (v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.26                 (u1_struct_0 @ X0))))
% 1.06/1.26          | (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4))
% 1.06/1.26          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v1_funct_1 @ X3)
% 1.06/1.26          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.26          | (v2_struct_0 @ X4)
% 1.06/1.26          | ~ (l1_pre_topc @ X2)
% 1.06/1.26          | ~ (v2_pre_topc @ X2)
% 1.06/1.26          | (v2_struct_0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.26  thf('204', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.26         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.26              (k1_zfmisc_1 @ 
% 1.06/1.26               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['202', '203'])).
% 1.06/1.26  thf('205', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('207', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('209', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('210', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('211', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('212', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('213', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('214', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['204', '205', '206', '207', '208', '209', '210', '211', 
% 1.06/1.26                 '212', '213'])).
% 1.06/1.26  thf('215', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.26         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['201', '214'])).
% 1.06/1.26  thf('216', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26         | ~ (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['200', '215'])).
% 1.06/1.26  thf('217', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['199', '216'])).
% 1.06/1.26  thf('218', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['198', '217'])).
% 1.06/1.26  thf('219', plain,
% 1.06/1.26      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 1.06/1.26         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('220', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['218', '219'])).
% 1.06/1.26  thf('221', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('222', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['220', '221'])).
% 1.06/1.26  thf('223', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('224', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['222', '223'])).
% 1.06/1.26  thf('225', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('226', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_2 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ 
% 1.06/1.26                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['224', '225'])).
% 1.06/1.26  thf('227', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('228', plain,
% 1.06/1.26      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['226', '227'])).
% 1.06/1.26  thf('229', plain,
% 1.06/1.26      (~
% 1.06/1.26       ((m1_subset_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.26       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('230', plain,
% 1.06/1.26      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26        | (v1_funct_1 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('231', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.26      inference('split', [status(esa)], ['230'])).
% 1.06/1.26  thf('232', plain,
% 1.06/1.26      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.26        | (v1_funct_1 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('233', plain,
% 1.06/1.26      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.06/1.26      inference('split', [status(esa)], ['232'])).
% 1.06/1.26  thf('234', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['26'])).
% 1.06/1.26  thf('235', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['24'])).
% 1.06/1.26  thf('236', plain,
% 1.06/1.26      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['230'])).
% 1.06/1.26  thf('237', plain,
% 1.06/1.26      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 1.06/1.26      inference('split', [status(esa)], ['16'])).
% 1.06/1.26  thf('238', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 1.06/1.26         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['20'])).
% 1.06/1.26  thf('239', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('split', [status(esa)], ['18'])).
% 1.06/1.26  thf('240', plain,
% 1.06/1.26      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.26         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('split', [status(esa)], ['22'])).
% 1.06/1.26  thf('241', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.26         ((v2_struct_0 @ X0)
% 1.06/1.26          | ~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v2_struct_0 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.26          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4))
% 1.06/1.26          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.26               (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ X4 @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1))
% 1.06/1.26          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.26               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ X1 @ X0)
% 1.06/1.26          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | (v1_funct_1 @ 
% 1.06/1.26             (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.26          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.26          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (v1_funct_1 @ X3)
% 1.06/1.26          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.26          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.26          | (v2_struct_0 @ X4)
% 1.06/1.26          | ~ (l1_pre_topc @ X2)
% 1.06/1.26          | ~ (v2_pre_topc @ X2)
% 1.06/1.26          | (v2_struct_0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.26  thf('242', plain,
% 1.06/1.26      ((![X0 : $i]:
% 1.06/1.26          ((v2_struct_0 @ sk_A)
% 1.06/1.26           | ~ (v2_pre_topc @ sk_A)
% 1.06/1.26           | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26           | (v2_struct_0 @ sk_D)
% 1.06/1.26           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.26           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.26           | ~ (v1_funct_1 @ sk_C)
% 1.06/1.26           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.26                (k1_zfmisc_1 @ 
% 1.06/1.26                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26           | (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 1.06/1.26           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (k1_zfmisc_1 @ 
% 1.06/1.26                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26                sk_B)
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26           | (v2_struct_0 @ X0)
% 1.06/1.26           | ~ (l1_pre_topc @ sk_B)
% 1.06/1.26           | ~ (v2_pre_topc @ sk_B)
% 1.06/1.26           | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['240', '241'])).
% 1.06/1.26  thf('243', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('244', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('245', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('247', plain,
% 1.06/1.26      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('248', plain,
% 1.06/1.26      ((m1_subset_1 @ sk_C @ 
% 1.06/1.26        (k1_zfmisc_1 @ 
% 1.06/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('249', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('250', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('251', plain,
% 1.06/1.26      ((![X0 : $i]:
% 1.06/1.26          ((v2_struct_0 @ sk_A)
% 1.06/1.26           | (v2_struct_0 @ sk_D)
% 1.06/1.26           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.26           | (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 1.06/1.26           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (k1_zfmisc_1 @ 
% 1.06/1.26                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26                sk_B)
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26           | (v2_struct_0 @ X0)
% 1.06/1.26           | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)],
% 1.06/1.26                ['242', '243', '244', '245', '246', '247', '248', '249', '250'])).
% 1.06/1.26  thf('252', plain,
% 1.06/1.26      ((![X0 : $i]:
% 1.06/1.26          ((v2_struct_0 @ sk_B)
% 1.06/1.26           | (v2_struct_0 @ X0)
% 1.06/1.26           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26                sk_B)
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.26           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (k1_zfmisc_1 @ 
% 1.06/1.26                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26           | (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 1.06/1.26           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.26           | (v2_struct_0 @ sk_D)
% 1.06/1.26           | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['239', '251'])).
% 1.06/1.26  thf('253', plain,
% 1.06/1.26      ((![X0 : $i]:
% 1.06/1.26          ((v2_struct_0 @ sk_A)
% 1.06/1.26           | (v2_struct_0 @ sk_D)
% 1.06/1.26           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.26           | (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 1.06/1.26           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (k1_zfmisc_1 @ 
% 1.06/1.26                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.26           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26           | (v2_struct_0 @ X0)
% 1.06/1.26           | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['238', '252'])).
% 1.06/1.26  thf('254', plain,
% 1.06/1.26      ((![X0 : $i]:
% 1.06/1.26          ((v2_struct_0 @ sk_B)
% 1.06/1.26           | (v2_struct_0 @ X0)
% 1.06/1.26           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.26           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.26           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.26           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.26           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.26                (k1_zfmisc_1 @ 
% 1.06/1.26                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26           | (v1_funct_1 @ 
% 1.06/1.26              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 1.06/1.26           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.26           | (v2_struct_0 @ sk_D)
% 1.06/1.26           | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['237', '253'])).
% 1.06/1.26  thf('255', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.26         | (v1_funct_1 @ 
% 1.06/1.26            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26              sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.26         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['236', '254'])).
% 1.06/1.26  thf('256', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.26      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('257', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('258', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_1 @ 
% 1.06/1.26            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26              sk_B)
% 1.06/1.26         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('demod', [status(thm)], ['255', '256', '257'])).
% 1.06/1.26  thf('259', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.26         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26              sk_B)
% 1.06/1.26         | (v1_funct_1 @ 
% 1.06/1.26            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['235', '258'])).
% 1.06/1.26  thf('260', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v1_funct_1 @ 
% 1.06/1.26            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['234', '259'])).
% 1.06/1.26  thf('261', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v1_funct_1 @ 
% 1.06/1.26            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_A)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['233', '260'])).
% 1.06/1.26  thf('262', plain,
% 1.06/1.26      ((~ (v1_funct_1 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.26      inference('split', [status(esa)], ['63'])).
% 1.06/1.26  thf('263', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_A)
% 1.06/1.26         | (v2_struct_0 @ sk_D)
% 1.06/1.26         | (v2_struct_0 @ sk_E)
% 1.06/1.26         | (v2_struct_0 @ sk_B)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['261', '262'])).
% 1.06/1.26  thf('264', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('265', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['263', '264'])).
% 1.06/1.26  thf('266', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('267', plain,
% 1.06/1.26      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['265', '266'])).
% 1.06/1.26  thf('268', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('269', plain,
% 1.06/1.26      (((v2_struct_0 @ sk_E))
% 1.06/1.26         <= (~
% 1.06/1.26             ((v1_funct_1 @ 
% 1.06/1.26               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.26                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.26             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.26             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.26             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.26               sk_B)) & 
% 1.06/1.26             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26               (k1_zfmisc_1 @ 
% 1.06/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.26      inference('clc', [status(thm)], ['267', '268'])).
% 1.06/1.26  thf('270', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('271', plain,
% 1.06/1.26      (((v1_funct_1 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.26       ~
% 1.06/1.26       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['269', '270'])).
% 1.06/1.26  thf('272', plain,
% 1.06/1.26      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['31'])).
% 1.06/1.26  thf('273', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.26        | (v1_funct_2 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('274', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['273'])).
% 1.06/1.26  thf('275', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.26        | (v1_funct_2 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('276', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['275'])).
% 1.06/1.26  thf('277', plain,
% 1.06/1.26      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.26        | (v1_funct_2 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('278', plain,
% 1.06/1.26      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.26         (k1_zfmisc_1 @ 
% 1.06/1.26          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['277'])).
% 1.06/1.26  thf('279', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.26        | (v1_funct_2 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('280', plain,
% 1.06/1.26      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.26         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['279'])).
% 1.06/1.26  thf('281', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.26        | (v1_funct_2 @ 
% 1.06/1.26           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26           (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('282', plain,
% 1.06/1.26      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.26       ((v1_funct_2 @ 
% 1.06/1.26         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.26         (u1_struct_0 @ sk_B)))),
% 1.06/1.26      inference('split', [status(esa)], ['281'])).
% 1.06/1.26  thf('283', plain,
% 1.06/1.26      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.06/1.26         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.06/1.26      inference('split', [status(esa)], ['232'])).
% 1.06/1.27  thf('284', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['26'])).
% 1.06/1.27  thf('285', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['24'])).
% 1.06/1.27  thf('286', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['230'])).
% 1.06/1.27  thf('287', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 1.06/1.27      inference('split', [status(esa)], ['16'])).
% 1.06/1.27  thf('288', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['20'])).
% 1.06/1.27  thf('289', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['18'])).
% 1.06/1.27  thf('290', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['22'])).
% 1.06/1.27  thf('291', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.27         ((v2_struct_0 @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_struct_0 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4))
% 1.06/1.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.27               (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ X4 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1))
% 1.06/1.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ X1 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | (v1_funct_2 @ 
% 1.06/1.27             (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27             (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v1_funct_1 @ X3)
% 1.06/1.27          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.27          | (v2_struct_0 @ X4)
% 1.06/1.27          | ~ (l1_pre_topc @ X2)
% 1.06/1.27          | ~ (v2_pre_topc @ X2)
% 1.06/1.27          | (v2_struct_0 @ X2))),
% 1.06/1.27      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.27  thf('292', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27           | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | ~ (v1_funct_1 @ sk_C)
% 1.06/1.27           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (l1_pre_topc @ sk_B)
% 1.06/1.27           | ~ (v2_pre_topc @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['290', '291'])).
% 1.06/1.27  thf('293', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('294', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('295', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('296', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('297', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('298', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('299', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('300', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('301', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)],
% 1.06/1.27                ['292', '293', '294', '295', '296', '297', '298', '299', '300'])).
% 1.06/1.27  thf('302', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['289', '301'])).
% 1.06/1.27  thf('303', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['288', '302'])).
% 1.06/1.27  thf('304', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['287', '303'])).
% 1.06/1.27  thf('305', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (v1_funct_2 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['286', '304'])).
% 1.06/1.27  thf('306', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.27      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.27  thf('307', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('308', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v1_funct_2 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)], ['305', '306', '307'])).
% 1.06/1.27  thf('309', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | (v1_funct_2 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ sk_B))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['285', '308'])).
% 1.06/1.27  thf('310', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v1_funct_2 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['284', '309'])).
% 1.06/1.27  thf('311', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v1_funct_2 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (u1_struct_0 @ sk_B))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['283', '310'])).
% 1.06/1.27  thf('312', plain,
% 1.06/1.27      ((~ (v1_funct_2 @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['63'])).
% 1.06/1.27  thf('313', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['311', '312'])).
% 1.06/1.27  thf('314', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('315', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['313', '314'])).
% 1.06/1.27  thf('316', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('317', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['315', '316'])).
% 1.06/1.27  thf('318', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('319', plain,
% 1.06/1.27      (((v2_struct_0 @ sk_E))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['317', '318'])).
% 1.06/1.27  thf('320', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('321', plain,
% 1.06/1.27      (~
% 1.06/1.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.27       ((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['319', '320'])).
% 1.06/1.27  thf('322', plain,
% 1.06/1.27      (((v1_funct_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.27       ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.06/1.27      inference('split', [status(esa)], ['232'])).
% 1.06/1.27  thf('323', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27        | (v1_funct_2 @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('324', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.27       ((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['323'])).
% 1.06/1.27  thf('325', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27        | (m1_subset_1 @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_zfmisc_1 @ 
% 1.06/1.27            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27             (u1_struct_0 @ sk_B)))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('326', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.27       ((m1_subset_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B)))))),
% 1.06/1.27      inference('split', [status(esa)], ['325'])).
% 1.06/1.27  thf('327', plain,
% 1.06/1.27      (((v1_funct_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.27         <= (((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.27      inference('split', [status(esa)], ['16'])).
% 1.06/1.27  thf('328', plain,
% 1.06/1.27      (((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['29'])).
% 1.06/1.27  thf('329', plain,
% 1.06/1.27      (((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['31'])).
% 1.06/1.27  thf('330', plain,
% 1.06/1.27      (((m1_subset_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['4'])).
% 1.06/1.27  thf('331', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.27         ((v2_struct_0 @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_struct_0 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.27          | ~ (v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.27          | ~ (v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27                 (u1_struct_0 @ X0))))
% 1.06/1.27          | (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1))
% 1.06/1.27          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v1_funct_1 @ X3)
% 1.06/1.27          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.27          | (v2_struct_0 @ X4)
% 1.06/1.27          | ~ (l1_pre_topc @ X2)
% 1.06/1.27          | ~ (v2_pre_topc @ X2)
% 1.06/1.27          | (v2_struct_0 @ X2))),
% 1.06/1.27      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.27  thf('332', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.27         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.27         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['330', '331'])).
% 1.06/1.27  thf('333', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('334', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('335', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('336', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('337', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('338', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('339', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('340', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('341', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('342', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)],
% 1.06/1.27                ['332', '333', '334', '335', '336', '337', '338', '339', 
% 1.06/1.27                 '340', '341'])).
% 1.06/1.27  thf('343', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | ~ (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['329', '342'])).
% 1.06/1.27  thf('344', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['328', '343'])).
% 1.06/1.27  thf('345', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['327', '344'])).
% 1.06/1.27  thf('346', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.27      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.27  thf('347', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)], ['345', '346'])).
% 1.06/1.27  thf('348', plain,
% 1.06/1.27      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.06/1.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.06/1.27      inference('split', [status(esa)], ['63'])).
% 1.06/1.27  thf('349', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['347', '348'])).
% 1.06/1.27  thf('350', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('351', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['349', '350'])).
% 1.06/1.27  thf('352', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('353', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['351', '352'])).
% 1.06/1.27  thf('354', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('355', plain,
% 1.06/1.27      (((v2_struct_0 @ sk_E))
% 1.06/1.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['353', '354'])).
% 1.06/1.27  thf('356', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('357', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['355', '356'])).
% 1.06/1.27  thf('358', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('split', [status(esa)], ['29'])).
% 1.06/1.27  thf('359', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27        | (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('360', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('split', [status(esa)], ['359'])).
% 1.06/1.27  thf('361', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 1.06/1.27        | (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('362', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('split', [status(esa)], ['361'])).
% 1.06/1.27  thf('363', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27        | (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('364', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('split', [status(esa)], ['363'])).
% 1.06/1.27  thf('365', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27        | (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('366', plain,
% 1.06/1.27      (((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.27       ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.06/1.27      inference('split', [status(esa)], ['365'])).
% 1.06/1.27  thf('367', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27        | (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('368', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('split', [status(esa)], ['367'])).
% 1.06/1.27  thf('369', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 1.06/1.27        | (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('370', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('split', [status(esa)], ['369'])).
% 1.06/1.27  thf('371', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.06/1.27      inference('split', [status(esa)], ['232'])).
% 1.06/1.27  thf('372', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['26'])).
% 1.06/1.27  thf('373', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['24'])).
% 1.06/1.27  thf('374', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['230'])).
% 1.06/1.27  thf('375', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 1.06/1.27      inference('split', [status(esa)], ['16'])).
% 1.06/1.27  thf('376', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['20'])).
% 1.06/1.27  thf('377', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['18'])).
% 1.06/1.27  thf('378', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['22'])).
% 1.06/1.27  thf('379', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.27         ((v2_struct_0 @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_struct_0 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4))
% 1.06/1.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.27               (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ X4 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1))
% 1.06/1.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ X1 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | (v5_pre_topc @ 
% 1.06/1.27             (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27             (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v1_funct_1 @ X3)
% 1.06/1.27          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.27          | (v2_struct_0 @ X4)
% 1.06/1.27          | ~ (l1_pre_topc @ X2)
% 1.06/1.27          | ~ (v2_pre_topc @ X2)
% 1.06/1.27          | (v2_struct_0 @ X2))),
% 1.06/1.27      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.27  thf('380', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27           | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | ~ (v1_funct_1 @ sk_C)
% 1.06/1.27           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (l1_pre_topc @ sk_B)
% 1.06/1.27           | ~ (v2_pre_topc @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['378', '379'])).
% 1.06/1.27  thf('381', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('382', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('383', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('384', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('385', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('386', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('387', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('388', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('389', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)],
% 1.06/1.27                ['380', '381', '382', '383', '384', '385', '386', '387', '388'])).
% 1.06/1.27  thf('390', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['377', '389'])).
% 1.06/1.27  thf('391', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['376', '390'])).
% 1.06/1.27  thf('392', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['375', '391'])).
% 1.06/1.27  thf('393', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (v5_pre_topc @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['374', '392'])).
% 1.06/1.27  thf('394', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.27      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.27  thf('395', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('396', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v5_pre_topc @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)], ['393', '394', '395'])).
% 1.06/1.27  thf('397', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | (v5_pre_topc @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['373', '396'])).
% 1.06/1.27  thf('398', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v5_pre_topc @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['372', '397'])).
% 1.06/1.27  thf('399', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v5_pre_topc @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['371', '398'])).
% 1.06/1.27  thf('400', plain,
% 1.06/1.27      ((~ (v5_pre_topc @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['63'])).
% 1.06/1.27  thf('401', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['399', '400'])).
% 1.06/1.27  thf('402', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('403', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['401', '402'])).
% 1.06/1.27  thf('404', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('405', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['403', '404'])).
% 1.06/1.27  thf('406', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('407', plain,
% 1.06/1.27      (((v2_struct_0 @ sk_E))
% 1.06/1.27         <= (~
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['405', '406'])).
% 1.06/1.27  thf('408', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('409', plain,
% 1.06/1.27      (((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) | 
% 1.06/1.27       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['407', '408'])).
% 1.06/1.27  thf('410', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.06/1.27      inference('split', [status(esa)], ['232'])).
% 1.06/1.27  thf('411', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['26'])).
% 1.06/1.27  thf('412', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['24'])).
% 1.06/1.27  thf('413', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['230'])).
% 1.06/1.27  thf('414', plain,
% 1.06/1.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 1.06/1.27      inference('split', [status(esa)], ['16'])).
% 1.06/1.27  thf('415', plain,
% 1.06/1.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['20'])).
% 1.06/1.27  thf('416', plain,
% 1.06/1.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['18'])).
% 1.06/1.27  thf('417', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['22'])).
% 1.06/1.27  thf('418', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.27         ((v2_struct_0 @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_struct_0 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4))
% 1.06/1.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.27               (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ X4 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X4) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1))
% 1.06/1.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27               (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ X1 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | (m1_subset_1 @ 
% 1.06/1.27             (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27             (k1_zfmisc_1 @ 
% 1.06/1.27              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v1_funct_1 @ X3)
% 1.06/1.27          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.27          | (v2_struct_0 @ X4)
% 1.06/1.27          | ~ (l1_pre_topc @ X2)
% 1.06/1.27          | ~ (v2_pre_topc @ X2)
% 1.06/1.27          | (v2_struct_0 @ X2))),
% 1.06/1.27      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.27  thf('419', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27           | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | ~ (v1_funct_1 @ sk_C)
% 1.06/1.27           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (m1_subset_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27                (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (l1_pre_topc @ sk_B)
% 1.06/1.27           | ~ (v2_pre_topc @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['417', '418'])).
% 1.06/1.27  thf('420', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('421', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('422', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('423', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('424', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('425', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('426', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('427', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('428', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (m1_subset_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27                (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27                (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)],
% 1.06/1.27                ['419', '420', '421', '422', '423', '424', '425', '426', '427'])).
% 1.06/1.27  thf('429', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27                sk_B)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (m1_subset_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27                (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['416', '428'])).
% 1.06/1.27  thf('430', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (m1_subset_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27                (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['415', '429'])).
% 1.06/1.27  thf('431', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          ((v2_struct_0 @ sk_B)
% 1.06/1.27           | (v2_struct_0 @ X0)
% 1.06/1.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.27           | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 1.06/1.27           | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.27           | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 1.06/1.27           | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 1.06/1.27                (k1_zfmisc_1 @ 
% 1.06/1.27                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27           | (m1_subset_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 1.06/1.27                (u1_struct_0 @ sk_B))))
% 1.06/1.27           | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 1.06/1.27           | (v2_struct_0 @ sk_D)
% 1.06/1.27           | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['414', '430'])).
% 1.06/1.27  thf('432', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | (m1_subset_1 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['413', '431'])).
% 1.06/1.27  thf('433', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.27      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.27  thf('434', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('435', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (m1_subset_1 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)], ['432', '433', '434'])).
% 1.06/1.27  thf('436', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27              sk_B)
% 1.06/1.27         | (m1_subset_1 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['412', '435'])).
% 1.06/1.27  thf('437', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (m1_subset_1 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))))
% 1.06/1.27         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['411', '436'])).
% 1.06/1.27  thf('438', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (m1_subset_1 @ 
% 1.06/1.27            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['410', '437'])).
% 1.06/1.27  thf('439', plain,
% 1.06/1.27      ((~ (m1_subset_1 @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (k1_zfmisc_1 @ 
% 1.06/1.27            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27             (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['63'])).
% 1.06/1.27  thf('440', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['438', '439'])).
% 1.06/1.27  thf('441', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('442', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['440', '441'])).
% 1.06/1.27  thf('443', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('444', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['442', '443'])).
% 1.06/1.27  thf('445', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('446', plain,
% 1.06/1.27      (((v2_struct_0 @ sk_E))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 1.06/1.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 1.06/1.27               sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['444', '445'])).
% 1.06/1.27  thf('447', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('448', plain,
% 1.06/1.27      (~
% 1.06/1.27       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ((m1_subset_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 1.06/1.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['446', '447'])).
% 1.06/1.27  thf('449', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27        | (v1_funct_2 @ 
% 1.06/1.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('450', plain,
% 1.06/1.27      (((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 1.06/1.27      inference('split', [status(esa)], ['449'])).
% 1.06/1.27  thf('451', plain,
% 1.06/1.27      (((v1_funct_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E))))
% 1.06/1.27         <= (((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))))),
% 1.06/1.27      inference('split', [status(esa)], ['16'])).
% 1.06/1.27  thf('452', plain,
% 1.06/1.27      (((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))
% 1.06/1.27         <= (((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)))),
% 1.06/1.27      inference('split', [status(esa)], ['29'])).
% 1.06/1.27  thf('453', plain,
% 1.06/1.27      (((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('split', [status(esa)], ['31'])).
% 1.06/1.27  thf('454', plain,
% 1.06/1.27      (((m1_subset_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['4'])).
% 1.06/1.27  thf('455', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.27         ((v2_struct_0 @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_struct_0 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X1 @ X2)
% 1.06/1.27          | ~ (v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)))
% 1.06/1.27          | ~ (v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (k1_tsep_1 @ X2 @ X4 @ X1) @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ X2 @ X0 @ X3 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X2 @ X4 @ X1)) @ 
% 1.06/1.27                 (u1_struct_0 @ X0))))
% 1.06/1.27          | (m1_subset_1 @ (k2_tmap_1 @ X2 @ X0 @ X3 @ X1) @ 
% 1.06/1.27             (k1_zfmisc_1 @ 
% 1.06/1.27              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (m1_subset_1 @ X3 @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 1.06/1.27          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 1.06/1.27          | ~ (v1_funct_1 @ X3)
% 1.06/1.27          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 1.06/1.27          | ~ (m1_pre_topc @ X4 @ X2)
% 1.06/1.27          | (v2_struct_0 @ X4)
% 1.06/1.27          | ~ (l1_pre_topc @ X2)
% 1.06/1.27          | ~ (v2_pre_topc @ X2)
% 1.06/1.27          | (v2_struct_0 @ X2))),
% 1.06/1.27      inference('cnf', [status(esa)], [t129_tmap_1])).
% 1.06/1.27  thf('456', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.06/1.27         | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ sk_C)
% 1.06/1.27         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.27              (k1_zfmisc_1 @ 
% 1.06/1.27               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | ~ (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (l1_pre_topc @ sk_B)
% 1.06/1.27         | ~ (v2_pre_topc @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['454', '455'])).
% 1.06/1.27  thf('457', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('458', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('459', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('460', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 1.06/1.27      inference('clc', [status(thm)], ['56', '57'])).
% 1.06/1.27  thf('461', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('462', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('463', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('464', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('465', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('466', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('467', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | ~ (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | ~ (v1_funct_2 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (u1_struct_0 @ sk_B))
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('demod', [status(thm)],
% 1.06/1.27                ['456', '457', '458', '459', '460', '461', '462', '463', 
% 1.06/1.27                 '464', '465', '466'])).
% 1.06/1.27  thf('468', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | ~ (v5_pre_topc @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27              (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 1.06/1.27         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['453', '467'])).
% 1.06/1.27  thf('469', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | ~ (v1_funct_1 @ 
% 1.06/1.27              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['452', '468'])).
% 1.06/1.27  thf('470', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27            (k1_zfmisc_1 @ 
% 1.06/1.27             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_A)))
% 1.06/1.27         <= (((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['451', '469'])).
% 1.06/1.27  thf('471', plain,
% 1.06/1.27      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27           (k1_zfmisc_1 @ 
% 1.06/1.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('split', [status(esa)], ['63'])).
% 1.06/1.27  thf('472', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_A)
% 1.06/1.27         | (v2_struct_0 @ sk_D)
% 1.06/1.27         | (v2_struct_0 @ sk_E)
% 1.06/1.27         | (v2_struct_0 @ sk_B)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['470', '471'])).
% 1.06/1.27  thf('473', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('474', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['472', '473'])).
% 1.06/1.27  thf('475', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('476', plain,
% 1.06/1.27      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['474', '475'])).
% 1.06/1.27  thf('477', plain, (~ (v2_struct_0 @ sk_D)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('478', plain,
% 1.06/1.27      (((v2_struct_0 @ sk_E))
% 1.06/1.27         <= (~
% 1.06/1.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 1.06/1.27             ((v1_funct_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) & 
% 1.06/1.27             ((v1_funct_2 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (u1_struct_0 @ sk_B))) & 
% 1.06/1.27             ((v5_pre_topc @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)) & 
% 1.06/1.27             ((m1_subset_1 @ 
% 1.06/1.27               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 1.06/1.27                (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k2_zfmisc_1 @ 
% 1.06/1.27                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27                 (u1_struct_0 @ sk_B))))))),
% 1.06/1.27      inference('clc', [status(thm)], ['476', '477'])).
% 1.06/1.27  thf('479', plain, (~ (v2_struct_0 @ sk_E)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('480', plain,
% 1.06/1.27      (~
% 1.06/1.27       ((v1_funct_2 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (u1_struct_0 @ sk_B))) | 
% 1.06/1.27       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v1_funct_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((m1_subset_1 @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27           (u1_struct_0 @ sk_B))))) | 
% 1.06/1.27       ~
% 1.06/1.27       ((v5_pre_topc @ 
% 1.06/1.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 1.06/1.27         (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['478', '479'])).
% 1.06/1.27  thf('481', plain, ($false),
% 1.06/1.27      inference('sat_resolution*', [status(thm)],
% 1.06/1.27                ['1', '3', '5', '7', '9', '11', '13', '15', '17', '19', '21', 
% 1.06/1.27                 '23', '25', '27', '73', '104', '135', '166', '197', '228', 
% 1.06/1.27                 '229', '231', '271', '272', '274', '276', '278', '280', 
% 1.06/1.27                 '282', '321', '322', '324', '326', '357', '358', '360', 
% 1.06/1.27                 '362', '364', '366', '368', '370', '409', '448', '450', '480'])).
% 1.06/1.27  
% 1.06/1.27  % SZS output end Refutation
% 1.06/1.27  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
