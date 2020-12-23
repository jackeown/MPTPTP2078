%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1QwTviLdzJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:08 EST 2020

% Result     : Theorem 45.07s
% Output     : Refutation 45.07s
% Verified   : 
% Statistics : Number of formulae       :  303 (1971 expanded)
%              Number of leaves         :   35 ( 563 expanded)
%              Depth                    :   27
%              Number of atoms          : 4452 (125067 expanded)
%              Number of equality atoms :   35 ( 820 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(t132_tmap_1,conjecture,(
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
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                          & ( r4_tsep_1 @ A @ D @ E ) )
                       => ( ( ( v1_funct_1 @ C )
                            & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ C @ A @ B )
                            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( A
                              = ( k1_tsep_1 @ A @ D @ E ) )
                            & ( r4_tsep_1 @ A @ D @ E ) )
                         => ( ( ( v1_funct_1 @ C )
                              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ C @ A @ B )
                              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                          <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                              & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','6','9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

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

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( k2_tmap_1 @ X9 @ X7 @ X10 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['40','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X14 )
      | ( ( k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) @ X15 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,
    ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) @ X33 @ ( k3_tmap_1 @ X35 @ X32 @ X34 @ X34 @ X33 ) )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

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

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        | ( sk_C = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        | ( sk_C = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['44'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','102'])).

thf('104',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('114',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('116',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('121',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['111','123'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf('129',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['137'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['126','138'])).

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

thf('140',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ X31 @ X27 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ X28 @ X27 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( r4_tsep_1 @ X29 @ X31 @ X28 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('141',plain,(
    ! [X0: $i] :
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
      | ( v2_struct_0 @ sk_B ) ) ),
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

thf('148',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('151',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['42'])).

thf('152',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('154',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['154'])).

thf('156',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['149','155'])).

thf('157',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','6','9','10','11'])).

thf('160',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['42'])).

thf('161',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['134','135'])).

thf('163',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['163'])).

thf('165',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['158','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146','147','156','165','166','167'])).

thf('169',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['169'])).

thf('171',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['172'])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ) )).

thf('175',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v5_pre_topc @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X24 @ X25 @ X23 @ X26 ) @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180','181','182'])).

thf('184',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['173','183'])).

thf('185',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['171','184'])).

thf('186',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['186'])).

thf('188',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['111','123'])).

thf('190',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('193',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['42'])).

thf('194',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['119','120'])).

thf('196',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['196'])).

thf('198',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['191','197'])).

thf('199',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','6','9','10','11'])).

thf('202',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['42'])).

thf('203',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['119','120'])).

thf('205',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['205'])).

thf('207',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['200','206'])).

thf('208',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['126','138'])).

thf('209',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['149','155'])).

thf('210',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['158','164'])).

thf('211',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['188','189','198','207','208','209','210','211','212','213'])).

thf('215',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['187','214'])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','215'])).

thf('217',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['172'])).

thf('218',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['173','183'])).

thf('227',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('229',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['236'])).

thf('238',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['224','235','237'])).

thf('239',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['170','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','240'])).

thf('242',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['200','206'])).

thf('244',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['191','197'])).

thf('245',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['186'])).

thf('246',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['246'])).

thf('248',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['224','235','247'])).

thf('249',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['245','248'])).

thf('250',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['241','242','243','244','249','250','251','252'])).

thf('254',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('257',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['224','235'])).

thf('258',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['255','258'])).

thf('260',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    $false ),
    inference(demod,[status(thm)],['0','265'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1QwTviLdzJ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 45.07/45.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 45.07/45.27  % Solved by: fo/fo7.sh
% 45.07/45.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.07/45.27  % done 5810 iterations in 44.808s
% 45.07/45.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 45.07/45.27  % SZS output start Refutation
% 45.07/45.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 45.07/45.27  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 45.07/45.27  thf(sk_B_type, type, sk_B: $i).
% 45.07/45.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 45.07/45.27  thf(sk_E_type, type, sk_E: $i).
% 45.07/45.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 45.07/45.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 45.07/45.27  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 45.07/45.27  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 45.07/45.27  thf(sk_A_type, type, sk_A: $i).
% 45.07/45.27  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 45.07/45.27  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 45.07/45.27  thf(sk_C_type, type, sk_C: $i).
% 45.07/45.27  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 45.07/45.27  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 45.07/45.27  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 45.07/45.27  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 45.07/45.27  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 45.07/45.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 45.07/45.27  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 45.07/45.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 45.07/45.27  thf(sk_D_type, type, sk_D: $i).
% 45.07/45.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 45.07/45.27  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 45.07/45.27  thf(t132_tmap_1, conjecture,
% 45.07/45.27    (![A:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 45.07/45.27       ( ![B:$i]:
% 45.07/45.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 45.07/45.27             ( l1_pre_topc @ B ) ) =>
% 45.07/45.27           ( ![C:$i]:
% 45.07/45.27             ( ( ( v1_funct_1 @ C ) & 
% 45.07/45.27                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                 ( m1_subset_1 @
% 45.07/45.27                   C @ 
% 45.07/45.27                   ( k1_zfmisc_1 @
% 45.07/45.27                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 45.07/45.27               ( ![D:$i]:
% 45.07/45.27                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 45.07/45.27                   ( ![E:$i]:
% 45.07/45.27                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 45.07/45.27                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 45.07/45.27                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 45.07/45.27                         ( ( ( v1_funct_1 @ C ) & 
% 45.07/45.27                             ( v1_funct_2 @
% 45.07/45.27                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                             ( v5_pre_topc @ C @ A @ B ) & 
% 45.07/45.27                             ( m1_subset_1 @
% 45.07/45.27                               C @ 
% 45.07/45.27                               ( k1_zfmisc_1 @
% 45.07/45.27                                 ( k2_zfmisc_1 @
% 45.07/45.27                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 45.07/45.27                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 45.07/45.27                             ( v1_funct_2 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 45.07/45.27                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                             ( v5_pre_topc @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 45.07/45.27                             ( m1_subset_1 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 45.07/45.27                               ( k1_zfmisc_1 @
% 45.07/45.27                                 ( k2_zfmisc_1 @
% 45.07/45.27                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 45.07/45.27                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 45.07/45.27                             ( v1_funct_2 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 45.07/45.27                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                             ( v5_pre_topc @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 45.07/45.27                             ( m1_subset_1 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 45.07/45.27                               ( k1_zfmisc_1 @
% 45.07/45.27                                 ( k2_zfmisc_1 @
% 45.07/45.27                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 45.07/45.27  thf(zf_stmt_0, negated_conjecture,
% 45.07/45.27    (~( ![A:$i]:
% 45.07/45.27        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 45.07/45.27            ( l1_pre_topc @ A ) ) =>
% 45.07/45.27          ( ![B:$i]:
% 45.07/45.27            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 45.07/45.27                ( l1_pre_topc @ B ) ) =>
% 45.07/45.27              ( ![C:$i]:
% 45.07/45.27                ( ( ( v1_funct_1 @ C ) & 
% 45.07/45.27                    ( v1_funct_2 @
% 45.07/45.27                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                    ( m1_subset_1 @
% 45.07/45.27                      C @ 
% 45.07/45.27                      ( k1_zfmisc_1 @
% 45.07/45.27                        ( k2_zfmisc_1 @
% 45.07/45.27                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 45.07/45.27                  ( ![D:$i]:
% 45.07/45.27                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 45.07/45.27                      ( ![E:$i]:
% 45.07/45.27                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 45.07/45.27                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 45.07/45.27                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 45.07/45.27                            ( ( ( v1_funct_1 @ C ) & 
% 45.07/45.27                                ( v1_funct_2 @
% 45.07/45.27                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                                ( v5_pre_topc @ C @ A @ B ) & 
% 45.07/45.27                                ( m1_subset_1 @
% 45.07/45.27                                  C @ 
% 45.07/45.27                                  ( k1_zfmisc_1 @
% 45.07/45.27                                    ( k2_zfmisc_1 @
% 45.07/45.27                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 45.07/45.27                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 45.07/45.27                                ( v1_funct_2 @
% 45.07/45.27                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 45.07/45.27                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                                ( v5_pre_topc @
% 45.07/45.27                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 45.07/45.27                                ( m1_subset_1 @
% 45.07/45.27                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 45.07/45.27                                  ( k1_zfmisc_1 @
% 45.07/45.27                                    ( k2_zfmisc_1 @
% 45.07/45.27                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 45.07/45.27                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 45.07/45.27                                ( v1_funct_2 @
% 45.07/45.27                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 45.07/45.27                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                                ( v5_pre_topc @
% 45.07/45.27                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 45.07/45.27                                ( m1_subset_1 @
% 45.07/45.27                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 45.07/45.27                                  ( k1_zfmisc_1 @
% 45.07/45.27                                    ( k2_zfmisc_1 @
% 45.07/45.27                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 45.07/45.27    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 45.07/45.27  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('1', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(dt_k2_tmap_1, axiom,
% 45.07/45.27    (![A:$i,B:$i,C:$i,D:$i]:
% 45.07/45.27     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 45.07/45.27         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27         ( m1_subset_1 @
% 45.07/45.27           C @ 
% 45.07/45.27           ( k1_zfmisc_1 @
% 45.07/45.27             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 45.07/45.27         ( l1_struct_0 @ D ) ) =>
% 45.07/45.27       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 45.07/45.27         ( v1_funct_2 @
% 45.07/45.27           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 45.07/45.27           ( u1_struct_0 @ B ) ) & 
% 45.07/45.27         ( m1_subset_1 @
% 45.07/45.27           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 45.07/45.27           ( k1_zfmisc_1 @
% 45.07/45.27             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 45.07/45.27  thf('2', plain,
% 45.07/45.27      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 45.07/45.27         (~ (m1_subset_1 @ X19 @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 45.07/45.27          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 45.07/45.27          | ~ (v1_funct_1 @ X19)
% 45.07/45.27          | ~ (l1_struct_0 @ X21)
% 45.07/45.27          | ~ (l1_struct_0 @ X20)
% 45.07/45.27          | ~ (l1_struct_0 @ X22)
% 45.07/45.27          | (v1_funct_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22)))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 45.07/45.27  thf('3', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (l1_struct_0 @ X0)
% 45.07/45.27          | ~ (l1_struct_0 @ sk_A)
% 45.07/45.27          | ~ (l1_struct_0 @ sk_B)
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['1', '2'])).
% 45.07/45.27  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(dt_l1_pre_topc, axiom,
% 45.07/45.27    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 45.07/45.27  thf('5', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 45.07/45.27  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 45.07/45.27      inference('sup-', [status(thm)], ['4', '5'])).
% 45.07/45.27  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('8', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 45.07/45.27  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 45.07/45.27      inference('sup-', [status(thm)], ['7', '8'])).
% 45.07/45.27  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('11', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('12', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['3', '6', '9', '10', '11'])).
% 45.07/45.27  thf('13', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('14', plain,
% 45.07/45.27      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 45.07/45.27         (~ (m1_subset_1 @ X19 @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 45.07/45.27          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 45.07/45.27          | ~ (v1_funct_1 @ X19)
% 45.07/45.27          | ~ (l1_struct_0 @ X21)
% 45.07/45.27          | ~ (l1_struct_0 @ X20)
% 45.07/45.27          | ~ (l1_struct_0 @ X22)
% 45.07/45.27          | (v1_funct_2 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 45.07/45.27             (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 45.07/45.27  thf('15', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (l1_struct_0 @ X0)
% 45.07/45.27          | ~ (l1_struct_0 @ sk_A)
% 45.07/45.27          | ~ (l1_struct_0 @ sk_B)
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['13', '14'])).
% 45.07/45.27  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 45.07/45.27      inference('sup-', [status(thm)], ['4', '5'])).
% 45.07/45.27  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 45.07/45.27      inference('sup-', [status(thm)], ['7', '8'])).
% 45.07/45.27  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('19', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('20', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 45.07/45.27  thf('21', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(dt_k1_tsep_1, axiom,
% 45.07/45.27    (![A:$i,B:$i,C:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 45.07/45.27         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 45.07/45.27         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 45.07/45.27       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 45.07/45.27         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 45.07/45.27         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 45.07/45.27  thf('23', plain,
% 45.07/45.27      (![X16 : $i, X17 : $i, X18 : $i]:
% 45.07/45.27         (~ (m1_pre_topc @ X16 @ X17)
% 45.07/45.27          | (v2_struct_0 @ X16)
% 45.07/45.27          | ~ (l1_pre_topc @ X17)
% 45.07/45.27          | (v2_struct_0 @ X17)
% 45.07/45.27          | (v2_struct_0 @ X18)
% 45.07/45.27          | ~ (m1_pre_topc @ X18 @ X17)
% 45.07/45.27          | (m1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X18) @ X17))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 45.07/45.27  thf('24', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D))),
% 45.07/45.27      inference('sup-', [status(thm)], ['22', '23'])).
% 45.07/45.27  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('26', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D))),
% 45.07/45.27      inference('demod', [status(thm)], ['24', '25'])).
% 45.07/45.27  thf('27', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 45.07/45.27      inference('sup-', [status(thm)], ['21', '26'])).
% 45.07/45.27  thf('28', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('29', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (m1_pre_topc @ sk_A @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)], ['27', '28'])).
% 45.07/45.27  thf('30', plain,
% 45.07/45.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 45.07/45.27        | (m1_subset_1 @ sk_C @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('31', plain,
% 45.07/45.27      (((m1_subset_1 @ sk_C @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['30'])).
% 45.07/45.27  thf(d4_tmap_1, axiom,
% 45.07/45.27    (![A:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 45.07/45.27       ( ![B:$i]:
% 45.07/45.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 45.07/45.27             ( l1_pre_topc @ B ) ) =>
% 45.07/45.27           ( ![C:$i]:
% 45.07/45.27             ( ( ( v1_funct_1 @ C ) & 
% 45.07/45.27                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                 ( m1_subset_1 @
% 45.07/45.27                   C @ 
% 45.07/45.27                   ( k1_zfmisc_1 @
% 45.07/45.27                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 45.07/45.27               ( ![D:$i]:
% 45.07/45.27                 ( ( m1_pre_topc @ D @ A ) =>
% 45.07/45.27                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 45.07/45.27                     ( k2_partfun1 @
% 45.07/45.27                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 45.07/45.27                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 45.07/45.27  thf('32', plain,
% 45.07/45.27      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X7)
% 45.07/45.27          | ~ (v2_pre_topc @ X7)
% 45.07/45.27          | ~ (l1_pre_topc @ X7)
% 45.07/45.27          | ~ (m1_pre_topc @ X8 @ X9)
% 45.07/45.27          | ((k2_tmap_1 @ X9 @ X7 @ X10 @ X8)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10 @ 
% 45.07/45.27                 (u1_struct_0 @ X8)))
% 45.07/45.27          | ~ (m1_subset_1 @ X10 @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 45.07/45.27          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 45.07/45.27          | ~ (v1_funct_1 @ X10)
% 45.07/45.27          | ~ (l1_pre_topc @ X9)
% 45.07/45.27          | ~ (v2_pre_topc @ X9)
% 45.07/45.27          | (v2_struct_0 @ X9))),
% 45.07/45.27      inference('cnf', [status(esa)], [d4_tmap_1])).
% 45.07/45.27  thf('33', plain,
% 45.07/45.27      ((![X0 : $i]:
% 45.07/45.27          ((v2_struct_0 @ sk_A)
% 45.07/45.27           | ~ (v2_pre_topc @ sk_A)
% 45.07/45.27           | ~ (l1_pre_topc @ sk_A)
% 45.07/45.27           | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27           | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 45.07/45.27               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                  sk_C @ (u1_struct_0 @ X0)))
% 45.07/45.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27           | ~ (l1_pre_topc @ sk_B)
% 45.07/45.27           | ~ (v2_pre_topc @ sk_B)
% 45.07/45.27           | (v2_struct_0 @ sk_B)))
% 45.07/45.27         <= (((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['31', '32'])).
% 45.07/45.27  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('37', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('40', plain,
% 45.07/45.27      ((![X0 : $i]:
% 45.07/45.27          ((v2_struct_0 @ sk_A)
% 45.07/45.27           | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 45.07/45.27               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                  sk_C @ (u1_struct_0 @ X0)))
% 45.07/45.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27           | (v2_struct_0 @ sk_B)))
% 45.07/45.27         <= (((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('demod', [status(thm)],
% 45.07/45.27                ['33', '34', '35', '36', '37', '38', '39'])).
% 45.07/45.27  thf('41', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('42', plain,
% 45.07/45.27      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27             sk_B)
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 45.07/45.27        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27             sk_B)
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 45.07/45.27        | ~ (m1_subset_1 @ sk_C @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 45.07/45.27        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('43', plain,
% 45.07/45.27      ((~ (m1_subset_1 @ sk_C @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (~
% 45.07/45.27             ((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('44', plain,
% 45.07/45.27      (((m1_subset_1 @ sk_C @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['41', '43'])).
% 45.07/45.27  thf('45', plain,
% 45.07/45.27      (((m1_subset_1 @ sk_C @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['44'])).
% 45.07/45.27  thf('46', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ sk_A)
% 45.07/45.27          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                 sk_C @ (u1_struct_0 @ X0)))
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['40', '45'])).
% 45.07/45.27  thf('47', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 45.07/45.27            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27               sk_C @ (u1_struct_0 @ sk_A)))
% 45.07/45.27        | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('sup-', [status(thm)], ['29', '46'])).
% 45.07/45.27  thf('48', plain,
% 45.07/45.27      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 45.07/45.27          = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27             sk_C @ (u1_struct_0 @ sk_A)))
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('simplify', [status(thm)], ['47'])).
% 45.07/45.27  thf('49', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (m1_pre_topc @ sk_A @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)], ['27', '28'])).
% 45.07/45.27  thf('50', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (m1_pre_topc @ sk_A @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)], ['27', '28'])).
% 45.07/45.27  thf('51', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(d5_tmap_1, axiom,
% 45.07/45.27    (![A:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 45.07/45.27       ( ![B:$i]:
% 45.07/45.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 45.07/45.27             ( l1_pre_topc @ B ) ) =>
% 45.07/45.27           ( ![C:$i]:
% 45.07/45.27             ( ( m1_pre_topc @ C @ A ) =>
% 45.07/45.27               ( ![D:$i]:
% 45.07/45.27                 ( ( m1_pre_topc @ D @ A ) =>
% 45.07/45.27                   ( ![E:$i]:
% 45.07/45.27                     ( ( ( v1_funct_1 @ E ) & 
% 45.07/45.27                         ( v1_funct_2 @
% 45.07/45.27                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                         ( m1_subset_1 @
% 45.07/45.27                           E @ 
% 45.07/45.27                           ( k1_zfmisc_1 @
% 45.07/45.27                             ( k2_zfmisc_1 @
% 45.07/45.27                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 45.07/45.27                       ( ( m1_pre_topc @ D @ C ) =>
% 45.07/45.27                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 45.07/45.27                           ( k2_partfun1 @
% 45.07/45.27                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 45.07/45.27                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 45.07/45.27  thf('52', plain,
% 45.07/45.27      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X11)
% 45.07/45.27          | ~ (v2_pre_topc @ X11)
% 45.07/45.27          | ~ (l1_pre_topc @ X11)
% 45.07/45.27          | ~ (m1_pre_topc @ X12 @ X13)
% 45.07/45.27          | ~ (m1_pre_topc @ X12 @ X14)
% 45.07/45.27          | ((k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11) @ 
% 45.07/45.27                 X15 @ (u1_struct_0 @ X12)))
% 45.07/45.27          | ~ (m1_subset_1 @ X15 @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))))
% 45.07/45.27          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))
% 45.07/45.27          | ~ (v1_funct_1 @ X15)
% 45.07/45.27          | ~ (m1_pre_topc @ X14 @ X13)
% 45.07/45.27          | ~ (l1_pre_topc @ X13)
% 45.07/45.27          | ~ (v2_pre_topc @ X13)
% 45.07/45.27          | (v2_struct_0 @ X13))),
% 45.07/45.27      inference('cnf', [status(esa)], [d5_tmap_1])).
% 45.07/45.27  thf('53', plain,
% 45.07/45.27      (![X0 : $i, X1 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X0)
% 45.07/45.27          | ~ (v2_pre_topc @ X0)
% 45.07/45.27          | ~ (l1_pre_topc @ X0)
% 45.07/45.27          | ~ (m1_pre_topc @ sk_A @ X0)
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                 sk_C @ (u1_struct_0 @ X1)))
% 45.07/45.27          | ~ (m1_pre_topc @ X1 @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ X1 @ X0)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_B)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_B)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('sup-', [status(thm)], ['51', '52'])).
% 45.07/45.27  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('55', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('57', plain, ((v2_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('58', plain,
% 45.07/45.27      (![X0 : $i, X1 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X0)
% 45.07/45.27          | ~ (v2_pre_topc @ X0)
% 45.07/45.27          | ~ (l1_pre_topc @ X0)
% 45.07/45.27          | ~ (m1_pre_topc @ sk_A @ X0)
% 45.07/45.27          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                 sk_C @ (u1_struct_0 @ X1)))
% 45.07/45.27          | ~ (m1_pre_topc @ X1 @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ X1 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 45.07/45.27  thf('59', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ sk_E)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D)
% 45.07/45.27          | (v2_struct_0 @ sk_B)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                 sk_C @ (u1_struct_0 @ X0)))
% 45.07/45.27          | ~ (l1_pre_topc @ sk_A)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('sup-', [status(thm)], ['50', '58'])).
% 45.07/45.27  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('62', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ sk_E)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D)
% 45.07/45.27          | (v2_struct_0 @ sk_B)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 45.07/45.27              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27                 sk_C @ (u1_struct_0 @ X0)))
% 45.07/45.27          | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)], ['59', '60', '61'])).
% 45.07/45.27  thf('63', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 45.07/45.27            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27               sk_C @ (u1_struct_0 @ X0)))
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_B)
% 45.07/45.27          | (v2_struct_0 @ sk_D)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('simplify', [status(thm)], ['62'])).
% 45.07/45.27  thf('64', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 45.07/45.27            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27               sk_C @ (u1_struct_0 @ sk_A))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['49', '63'])).
% 45.07/45.27  thf('65', plain,
% 45.07/45.27      ((((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 45.07/45.27          = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27             sk_C @ (u1_struct_0 @ sk_A)))
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('simplify', [status(thm)], ['64'])).
% 45.07/45.27  thf('66', plain,
% 45.07/45.27      ((((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 45.07/45.27          = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('sup+', [status(thm)], ['48', '65'])).
% 45.07/45.27  thf('67', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 45.07/45.27            = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('simplify', [status(thm)], ['66'])).
% 45.07/45.27  thf('68', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (m1_pre_topc @ sk_A @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)], ['27', '28'])).
% 45.07/45.27  thf('69', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(t74_tmap_1, axiom,
% 45.07/45.27    (![A:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 45.07/45.27       ( ![B:$i]:
% 45.07/45.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 45.07/45.27             ( l1_pre_topc @ B ) ) =>
% 45.07/45.27           ( ![C:$i]:
% 45.07/45.27             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 45.07/45.27               ( ![D:$i]:
% 45.07/45.27                 ( ( ( v1_funct_1 @ D ) & 
% 45.07/45.27                     ( v1_funct_2 @
% 45.07/45.27                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                     ( m1_subset_1 @
% 45.07/45.27                       D @ 
% 45.07/45.27                       ( k1_zfmisc_1 @
% 45.07/45.27                         ( k2_zfmisc_1 @
% 45.07/45.27                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 45.07/45.27                   ( r2_funct_2 @
% 45.07/45.27                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 45.07/45.27                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 45.07/45.27  thf('70', plain,
% 45.07/45.27      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X32)
% 45.07/45.27          | ~ (v2_pre_topc @ X32)
% 45.07/45.27          | ~ (l1_pre_topc @ X32)
% 45.07/45.27          | ~ (v1_funct_1 @ X33)
% 45.07/45.27          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 45.07/45.27          | ~ (m1_subset_1 @ X33 @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 45.07/45.27          | (r2_funct_2 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32) @ X33 @ 
% 45.07/45.27             (k3_tmap_1 @ X35 @ X32 @ X34 @ X34 @ X33))
% 45.07/45.27          | ~ (m1_pre_topc @ X34 @ X35)
% 45.07/45.27          | (v2_struct_0 @ X34)
% 45.07/45.27          | ~ (l1_pre_topc @ X35)
% 45.07/45.27          | ~ (v2_pre_topc @ X35)
% 45.07/45.27          | (v2_struct_0 @ X35))),
% 45.07/45.27      inference('cnf', [status(esa)], [t74_tmap_1])).
% 45.07/45.27  thf('71', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X0)
% 45.07/45.27          | ~ (v2_pre_topc @ X0)
% 45.07/45.27          | ~ (l1_pre_topc @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ sk_A @ X0)
% 45.07/45.27          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C))
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_B)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_B)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('sup-', [status(thm)], ['69', '70'])).
% 45.07/45.27  thf('72', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('75', plain, ((v2_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('76', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X0)
% 45.07/45.27          | ~ (v2_pre_topc @ X0)
% 45.07/45.27          | ~ (l1_pre_topc @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | ~ (m1_pre_topc @ sk_A @ X0)
% 45.07/45.27          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C))
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 45.07/45.27  thf('77', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C))
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | ~ (l1_pre_topc @ sk_A)
% 45.07/45.27        | ~ (v2_pre_topc @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('sup-', [status(thm)], ['68', '76'])).
% 45.07/45.27  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('80', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C))
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)], ['77', '78', '79'])).
% 45.07/45.27  thf('81', plain,
% 45.07/45.27      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27         (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C))
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('simplify', [status(thm)], ['80'])).
% 45.07/45.27  thf('82', plain,
% 45.07/45.27      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27         (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('sup+', [status(thm)], ['67', '81'])).
% 45.07/45.27  thf('83', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('simplify', [status(thm)], ['82'])).
% 45.07/45.27  thf('84', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('85', plain,
% 45.07/45.27      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 45.07/45.27         (~ (m1_subset_1 @ X19 @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 45.07/45.27          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 45.07/45.27          | ~ (v1_funct_1 @ X19)
% 45.07/45.27          | ~ (l1_struct_0 @ X21)
% 45.07/45.27          | ~ (l1_struct_0 @ X20)
% 45.07/45.27          | ~ (l1_struct_0 @ X22)
% 45.07/45.27          | (m1_subset_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 45.07/45.27  thf('86', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (l1_struct_0 @ X0)
% 45.07/45.27          | ~ (l1_struct_0 @ sk_A)
% 45.07/45.27          | ~ (l1_struct_0 @ sk_B)
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['84', '85'])).
% 45.07/45.27  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 45.07/45.27      inference('sup-', [status(thm)], ['4', '5'])).
% 45.07/45.27  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 45.07/45.27      inference('sup-', [status(thm)], ['7', '8'])).
% 45.07/45.27  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('90', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('91', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 45.07/45.27  thf('92', plain,
% 45.07/45.27      (((m1_subset_1 @ sk_C @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['30'])).
% 45.07/45.27  thf(redefinition_r2_funct_2, axiom,
% 45.07/45.27    (![A:$i,B:$i,C:$i,D:$i]:
% 45.07/45.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 45.07/45.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 45.07/45.27         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 45.07/45.27         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 45.07/45.27       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 45.07/45.27  thf('93', plain,
% 45.07/45.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.07/45.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 45.07/45.27          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 45.07/45.27          | ~ (v1_funct_1 @ X0)
% 45.07/45.27          | ~ (v1_funct_1 @ X3)
% 45.07/45.27          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 45.07/45.27          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 45.07/45.27          | ((X0) = (X3))
% 45.07/45.27          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 45.07/45.27      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 45.07/45.27  thf('94', plain,
% 45.07/45.27      ((![X0 : $i]:
% 45.07/45.27          (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27              sk_C @ X0)
% 45.07/45.27           | ((sk_C) = (X0))
% 45.07/45.27           | ~ (m1_subset_1 @ X0 @ 
% 45.07/45.27                (k1_zfmisc_1 @ 
% 45.07/45.27                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27           | ~ (v1_funct_1 @ X0)
% 45.07/45.27           | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27         <= (((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['92', '93'])).
% 45.07/45.27  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('96', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('97', plain,
% 45.07/45.27      ((![X0 : $i]:
% 45.07/45.27          (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 45.07/45.27              sk_C @ X0)
% 45.07/45.27           | ((sk_C) = (X0))
% 45.07/45.27           | ~ (m1_subset_1 @ X0 @ 
% 45.07/45.27                (k1_zfmisc_1 @ 
% 45.07/45.27                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27           | ~ (v1_funct_1 @ X0)))
% 45.07/45.27         <= (((m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('demod', [status(thm)], ['94', '95', '96'])).
% 45.07/45.27  thf('98', plain,
% 45.07/45.27      (((m1_subset_1 @ sk_C @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['44'])).
% 45.07/45.27  thf('99', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27             X0)
% 45.07/45.27          | ((sk_C) = (X0))
% 45.07/45.27          | ~ (m1_subset_1 @ X0 @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v1_funct_1 @ X0))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 45.07/45.27  thf('100', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_A)
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 45.07/45.27             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['91', '99'])).
% 45.07/45.27  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 45.07/45.27      inference('sup-', [status(thm)], ['4', '5'])).
% 45.07/45.27  thf('102', plain,
% 45.07/45.27      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 45.07/45.27             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 45.07/45.27             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('demod', [status(thm)], ['100', '101'])).
% 45.07/45.27  thf('103', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 45.07/45.27             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['83', '102'])).
% 45.07/45.27  thf('104', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_A)
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('sup-', [status(thm)], ['20', '103'])).
% 45.07/45.27  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 45.07/45.27      inference('sup-', [status(thm)], ['4', '5'])).
% 45.07/45.27  thf('106', plain,
% 45.07/45.27      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('demod', [status(thm)], ['104', '105'])).
% 45.07/45.27  thf('107', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['12', '106'])).
% 45.07/45.27  thf('108', plain, ((l1_struct_0 @ sk_A)),
% 45.07/45.27      inference('sup-', [status(thm)], ['4', '5'])).
% 45.07/45.27  thf('109', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 45.07/45.27      inference('demod', [status(thm)], ['107', '108'])).
% 45.07/45.27  thf('110', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('111', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['110'])).
% 45.07/45.27  thf('112', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 45.07/45.27  thf('113', plain,
% 45.07/45.27      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (~
% 45.07/45.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('114', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_E))
% 45.07/45.27         <= (~
% 45.07/45.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['112', '113'])).
% 45.07/45.27  thf('115', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(dt_m1_pre_topc, axiom,
% 45.07/45.27    (![A:$i]:
% 45.07/45.27     ( ( l1_pre_topc @ A ) =>
% 45.07/45.27       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 45.07/45.27  thf('116', plain,
% 45.07/45.27      (![X5 : $i, X6 : $i]:
% 45.07/45.27         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 45.07/45.27  thf('117', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 45.07/45.27      inference('sup-', [status(thm)], ['115', '116'])).
% 45.07/45.27  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('119', plain, ((l1_pre_topc @ sk_E)),
% 45.07/45.27      inference('demod', [status(thm)], ['117', '118'])).
% 45.07/45.27  thf('120', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 45.07/45.27  thf('121', plain, ((l1_struct_0 @ sk_E)),
% 45.07/45.27      inference('sup-', [status(thm)], ['119', '120'])).
% 45.07/45.27  thf('122', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('demod', [status(thm)], ['114', '121'])).
% 45.07/45.27  thf('123', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['122'])).
% 45.07/45.27  thf('124', plain,
% 45.07/45.27      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['111', '123'])).
% 45.07/45.27  thf('125', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('126', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['125'])).
% 45.07/45.27  thf('127', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 45.07/45.27  thf('128', plain,
% 45.07/45.27      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 45.07/45.27         <= (~
% 45.07/45.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('129', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_D))
% 45.07/45.27         <= (~
% 45.07/45.27             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['127', '128'])).
% 45.07/45.27  thf('130', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('131', plain,
% 45.07/45.27      (![X5 : $i, X6 : $i]:
% 45.07/45.27         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 45.07/45.27  thf('132', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 45.07/45.27      inference('sup-', [status(thm)], ['130', '131'])).
% 45.07/45.27  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('134', plain, ((l1_pre_topc @ sk_D)),
% 45.07/45.27      inference('demod', [status(thm)], ['132', '133'])).
% 45.07/45.27  thf('135', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 45.07/45.27      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 45.07/45.27  thf('136', plain, ((l1_struct_0 @ sk_D)),
% 45.07/45.27      inference('sup-', [status(thm)], ['134', '135'])).
% 45.07/45.27  thf('137', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('demod', [status(thm)], ['129', '136'])).
% 45.07/45.27  thf('138', plain,
% 45.07/45.27      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (k1_zfmisc_1 @ 
% 45.07/45.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['137'])).
% 45.07/45.27  thf('139', plain,
% 45.07/45.27      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['126', '138'])).
% 45.07/45.27  thf(t129_tmap_1, axiom,
% 45.07/45.27    (![A:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 45.07/45.27       ( ![B:$i]:
% 45.07/45.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 45.07/45.27             ( l1_pre_topc @ B ) ) =>
% 45.07/45.27           ( ![C:$i]:
% 45.07/45.27             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 45.07/45.27               ( ![D:$i]:
% 45.07/45.27                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 45.07/45.27                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 45.07/45.27                     ( ![E:$i]:
% 45.07/45.27                       ( ( ( v1_funct_1 @ E ) & 
% 45.07/45.27                           ( v1_funct_2 @
% 45.07/45.27                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                           ( m1_subset_1 @
% 45.07/45.27                             E @ 
% 45.07/45.27                             ( k1_zfmisc_1 @
% 45.07/45.27                               ( k2_zfmisc_1 @
% 45.07/45.27                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 45.07/45.27                         ( ( ( v1_funct_1 @
% 45.07/45.27                               ( k2_tmap_1 @
% 45.07/45.27                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 45.07/45.27                             ( v1_funct_2 @
% 45.07/45.27                               ( k2_tmap_1 @
% 45.07/45.27                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 45.07/45.27                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 45.07/45.27                               ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                             ( v5_pre_topc @
% 45.07/45.27                               ( k2_tmap_1 @
% 45.07/45.27                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 45.07/45.27                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 45.07/45.27                             ( m1_subset_1 @
% 45.07/45.27                               ( k2_tmap_1 @
% 45.07/45.27                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 45.07/45.27                               ( k1_zfmisc_1 @
% 45.07/45.27                                 ( k2_zfmisc_1 @
% 45.07/45.27                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 45.07/45.27                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 45.07/45.27                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 45.07/45.27                             ( v1_funct_2 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 45.07/45.27                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                             ( v5_pre_topc @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 45.07/45.27                             ( m1_subset_1 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 45.07/45.27                               ( k1_zfmisc_1 @
% 45.07/45.27                                 ( k2_zfmisc_1 @
% 45.07/45.27                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 45.07/45.27                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 45.07/45.27                             ( v1_funct_2 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 45.07/45.27                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27                             ( v5_pre_topc @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 45.07/45.27                             ( m1_subset_1 @
% 45.07/45.27                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 45.07/45.27                               ( k1_zfmisc_1 @
% 45.07/45.27                                 ( k2_zfmisc_1 @
% 45.07/45.27                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 45.07/45.27  thf('140', plain,
% 45.07/45.27      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 45.07/45.27         ((v2_struct_0 @ X27)
% 45.07/45.27          | ~ (v2_pre_topc @ X27)
% 45.07/45.27          | ~ (l1_pre_topc @ X27)
% 45.07/45.27          | (v2_struct_0 @ X28)
% 45.07/45.27          | ~ (m1_pre_topc @ X28 @ X29)
% 45.07/45.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31))
% 45.07/45.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ 
% 45.07/45.27               (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ X31 @ X27)
% 45.07/45.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 45.07/45.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28))
% 45.07/45.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ 
% 45.07/45.27               (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ X28 @ X27)
% 45.07/45.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 45.07/45.27          | (v5_pre_topc @ 
% 45.07/45.27             (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 45.07/45.27             (k1_tsep_1 @ X29 @ X31 @ X28) @ X27)
% 45.07/45.27          | ~ (m1_subset_1 @ X30 @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 45.07/45.27          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 45.07/45.27          | ~ (v1_funct_1 @ X30)
% 45.07/45.27          | ~ (r4_tsep_1 @ X29 @ X31 @ X28)
% 45.07/45.27          | ~ (m1_pre_topc @ X31 @ X29)
% 45.07/45.27          | (v2_struct_0 @ X31)
% 45.07/45.27          | ~ (l1_pre_topc @ X29)
% 45.07/45.27          | ~ (v2_pre_topc @ X29)
% 45.07/45.27          | (v2_struct_0 @ X29))),
% 45.07/45.27      inference('cnf', [status(esa)], [t129_tmap_1])).
% 45.07/45.27  thf('141', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ sk_A)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_A)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D)
% 45.07/45.27          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 45.07/45.27          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (m1_subset_1 @ sk_C @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | (v5_pre_topc @ 
% 45.07/45.27             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 45.07/45.27             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 45.07/45.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 45.07/45.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27               sk_B)
% 45.07/45.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_B)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_B)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('sup-', [status(thm)], ['139', '140'])).
% 45.07/45.27  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('144', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('146', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('147', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('148', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('149', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 45.07/45.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('split', [status(esa)], ['148'])).
% 45.07/45.27  thf('150', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 45.07/45.27  thf('151', plain,
% 45.07/45.27      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('152', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_D))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['150', '151'])).
% 45.07/45.27  thf('153', plain, ((l1_struct_0 @ sk_D)),
% 45.07/45.27      inference('sup-', [status(thm)], ['134', '135'])).
% 45.07/45.27  thf('154', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('demod', [status(thm)], ['152', '153'])).
% 45.07/45.27  thf('155', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['154'])).
% 45.07/45.27  thf('156', plain,
% 45.07/45.27      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['149', '155'])).
% 45.07/45.27  thf('157', plain,
% 45.07/45.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('158', plain,
% 45.07/45.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 45.07/45.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 45.07/45.27      inference('split', [status(esa)], ['157'])).
% 45.07/45.27  thf('159', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['3', '6', '9', '10', '11'])).
% 45.07/45.27  thf('160', plain,
% 45.07/45.27      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 45.07/45.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('161', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_D))
% 45.07/45.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['159', '160'])).
% 45.07/45.27  thf('162', plain, ((l1_struct_0 @ sk_D)),
% 45.07/45.27      inference('sup-', [status(thm)], ['134', '135'])).
% 45.07/45.27  thf('163', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 45.07/45.27      inference('demod', [status(thm)], ['161', '162'])).
% 45.07/45.27  thf('164', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['163'])).
% 45.07/45.27  thf('165', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['158', '164'])).
% 45.07/45.27  thf('166', plain, ((l1_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('167', plain, ((v2_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('168', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D)
% 45.07/45.27          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 45.07/45.27          | (v5_pre_topc @ 
% 45.07/45.27             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 45.07/45.27             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 45.07/45.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 45.07/45.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27               sk_B)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('demod', [status(thm)],
% 45.07/45.27                ['141', '142', '143', '144', '145', '146', '147', '156', 
% 45.07/45.27                 '165', '166', '167'])).
% 45.07/45.27  thf('169', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('170', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 45.07/45.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['169'])).
% 45.07/45.27  thf('171', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('172', plain,
% 45.07/45.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 45.07/45.27        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('173', plain,
% 45.07/45.27      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['172'])).
% 45.07/45.27  thf('174', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf(fc2_tmap_1, axiom,
% 45.07/45.27    (![A:$i,B:$i,C:$i,D:$i]:
% 45.07/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 45.07/45.27         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 45.07/45.27         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( v1_funct_1 @ C ) & 
% 45.07/45.27         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 45.07/45.27         ( v5_pre_topc @ C @ A @ B ) & 
% 45.07/45.27         ( m1_subset_1 @
% 45.07/45.27           C @ 
% 45.07/45.27           ( k1_zfmisc_1 @
% 45.07/45.27             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 45.07/45.27         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 45.07/45.27       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 45.07/45.27         ( v1_funct_2 @
% 45.07/45.27           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 45.07/45.27           ( u1_struct_0 @ B ) ) & 
% 45.07/45.27         ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ))).
% 45.07/45.27  thf('175', plain,
% 45.07/45.27      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 45.07/45.27         (~ (m1_subset_1 @ X23 @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 45.07/45.27          | ~ (v5_pre_topc @ X23 @ X24 @ X25)
% 45.07/45.27          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 45.07/45.27          | ~ (v1_funct_1 @ X23)
% 45.07/45.27          | ~ (l1_pre_topc @ X25)
% 45.07/45.27          | ~ (v2_pre_topc @ X25)
% 45.07/45.27          | (v2_struct_0 @ X25)
% 45.07/45.27          | ~ (l1_pre_topc @ X24)
% 45.07/45.27          | ~ (v2_pre_topc @ X24)
% 45.07/45.27          | (v2_struct_0 @ X24)
% 45.07/45.27          | (v2_struct_0 @ X26)
% 45.07/45.27          | ~ (m1_pre_topc @ X26 @ X24)
% 45.07/45.27          | (v5_pre_topc @ (k2_tmap_1 @ X24 @ X25 @ X23 @ X26) @ X26 @ X25))),
% 45.07/45.27      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 45.07/45.27  thf('176', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_A)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_B)
% 45.07/45.27          | ~ (v2_pre_topc @ sk_B)
% 45.07/45.27          | ~ (l1_pre_topc @ sk_B)
% 45.07/45.27          | ~ (v1_funct_1 @ sk_C)
% 45.07/45.27          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('sup-', [status(thm)], ['174', '175'])).
% 45.07/45.27  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('179', plain, ((v2_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('180', plain, ((l1_pre_topc @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('182', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('183', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_B)
% 45.07/45.27          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('demod', [status(thm)],
% 45.07/45.27                ['176', '177', '178', '179', '180', '181', '182'])).
% 45.07/45.27  thf('184', plain,
% 45.07/45.27      ((![X0 : $i]:
% 45.07/45.27          ((v2_struct_0 @ sk_B)
% 45.07/45.27           | (v2_struct_0 @ sk_A)
% 45.07/45.27           | (v2_struct_0 @ X0)
% 45.07/45.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['173', '183'])).
% 45.07/45.27  thf('185', plain,
% 45.07/45.27      ((((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 45.07/45.27         | (v2_struct_0 @ sk_D)
% 45.07/45.27         | (v2_struct_0 @ sk_A)
% 45.07/45.27         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['171', '184'])).
% 45.07/45.27  thf('186', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('187', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 45.07/45.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['186'])).
% 45.07/45.27  thf('188', plain,
% 45.07/45.27      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27           (k1_zfmisc_1 @ 
% 45.07/45.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27             sk_B)
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 45.07/45.27        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27             sk_B)
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 45.07/45.27        | ~ (m1_subset_1 @ sk_C @ 
% 45.07/45.27             (k1_zfmisc_1 @ 
% 45.07/45.27              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 45.07/45.27        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('189', plain,
% 45.07/45.27      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['111', '123'])).
% 45.07/45.27  thf('190', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('191', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 45.07/45.27         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('split', [status(esa)], ['190'])).
% 45.07/45.27  thf('192', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 45.07/45.27  thf('193', plain,
% 45.07/45.27      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('194', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_E))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['192', '193'])).
% 45.07/45.27  thf('195', plain, ((l1_struct_0 @ sk_E)),
% 45.07/45.27      inference('sup-', [status(thm)], ['119', '120'])).
% 45.07/45.27  thf('196', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('demod', [status(thm)], ['194', '195'])).
% 45.07/45.27  thf('197', plain,
% 45.07/45.27      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['196'])).
% 45.07/45.27  thf('198', plain,
% 45.07/45.27      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['191', '197'])).
% 45.07/45.27  thf('199', plain,
% 45.07/45.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 45.07/45.27        | (v1_funct_1 @ sk_C))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('200', plain,
% 45.07/45.27      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 45.07/45.27         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 45.07/45.27      inference('split', [status(esa)], ['199'])).
% 45.07/45.27  thf('201', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (l1_struct_0 @ X0))),
% 45.07/45.27      inference('demod', [status(thm)], ['3', '6', '9', '10', '11'])).
% 45.07/45.27  thf('202', plain,
% 45.07/45.27      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 45.07/45.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('203', plain,
% 45.07/45.27      ((~ (l1_struct_0 @ sk_E))
% 45.07/45.27         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 45.07/45.27      inference('sup-', [status(thm)], ['201', '202'])).
% 45.07/45.27  thf('204', plain, ((l1_struct_0 @ sk_E)),
% 45.07/45.27      inference('sup-', [status(thm)], ['119', '120'])).
% 45.07/45.27  thf('205', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 45.07/45.27      inference('demod', [status(thm)], ['203', '204'])).
% 45.07/45.27  thf('206', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['205'])).
% 45.07/45.27  thf('207', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['200', '206'])).
% 45.07/45.27  thf('208', plain,
% 45.07/45.27      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['126', '138'])).
% 45.07/45.27  thf('209', plain,
% 45.07/45.27      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 45.07/45.27        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['149', '155'])).
% 45.07/45.27  thf('210', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['158', '164'])).
% 45.07/45.27  thf('211', plain,
% 45.07/45.27      ((m1_subset_1 @ sk_C @ 
% 45.07/45.27        (k1_zfmisc_1 @ 
% 45.07/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('212', plain,
% 45.07/45.27      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('214', plain,
% 45.07/45.27      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 45.07/45.27        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27             sk_B)
% 45.07/45.27        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('demod', [status(thm)],
% 45.07/45.27                ['188', '189', '198', '207', '208', '209', '210', '211', 
% 45.07/45.27                 '212', '213'])).
% 45.07/45.27  thf('215', plain,
% 45.07/45.27      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 45.07/45.27         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 45.07/45.27              sk_B)))
% 45.07/45.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['187', '214'])).
% 45.07/45.27  thf('216', plain,
% 45.07/45.27      ((((v2_struct_0 @ sk_B)
% 45.07/45.27         | (v2_struct_0 @ sk_A)
% 45.07/45.27         | (v2_struct_0 @ sk_D)
% 45.07/45.27         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['185', '215'])).
% 45.07/45.27  thf('217', plain,
% 45.07/45.27      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['172'])).
% 45.07/45.27  thf('218', plain,
% 45.07/45.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('demod', [status(thm)], ['216', '217'])).
% 45.07/45.27  thf('219', plain, (~ (v2_struct_0 @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('220', plain,
% 45.07/45.27      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('clc', [status(thm)], ['218', '219'])).
% 45.07/45.27  thf('221', plain, (~ (v2_struct_0 @ sk_D)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('222', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_A))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('clc', [status(thm)], ['220', '221'])).
% 45.07/45.27  thf('223', plain, (~ (v2_struct_0 @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('224', plain,
% 45.07/45.27      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 45.07/45.27       ~
% 45.07/45.27       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 45.07/45.27      inference('sup-', [status(thm)], ['222', '223'])).
% 45.07/45.27  thf('225', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('226', plain,
% 45.07/45.27      ((![X0 : $i]:
% 45.07/45.27          ((v2_struct_0 @ sk_B)
% 45.07/45.27           | (v2_struct_0 @ sk_A)
% 45.07/45.27           | (v2_struct_0 @ X0)
% 45.07/45.27           | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)))
% 45.07/45.27         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['173', '183'])).
% 45.07/45.27  thf('227', plain,
% 45.07/45.27      ((((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 45.07/45.27         | (v2_struct_0 @ sk_E)
% 45.07/45.27         | (v2_struct_0 @ sk_A)
% 45.07/45.27         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['225', '226'])).
% 45.07/45.27  thf('228', plain,
% 45.07/45.27      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('229', plain,
% 45.07/45.27      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('sup-', [status(thm)], ['227', '228'])).
% 45.07/45.27  thf('230', plain, (~ (v2_struct_0 @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('231', plain,
% 45.07/45.27      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('clc', [status(thm)], ['229', '230'])).
% 45.07/45.27  thf('232', plain, (~ (v2_struct_0 @ sk_E)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('233', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_A))
% 45.07/45.27         <= (~
% 45.07/45.27             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)) & 
% 45.07/45.27             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('clc', [status(thm)], ['231', '232'])).
% 45.07/45.27  thf('234', plain, (~ (v2_struct_0 @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('235', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 45.07/45.27       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('sup-', [status(thm)], ['233', '234'])).
% 45.07/45.27  thf('236', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 45.07/45.27        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('237', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 45.07/45.27       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('split', [status(esa)], ['236'])).
% 45.07/45.27  thf('238', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['224', '235', '237'])).
% 45.07/45.27  thf('239', plain,
% 45.07/45.27      ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['170', '238'])).
% 45.07/45.27  thf('240', plain,
% 45.07/45.27      (![X0 : $i]:
% 45.07/45.27         ((v2_struct_0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ sk_D)
% 45.07/45.27          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 45.07/45.27          | (v5_pre_topc @ 
% 45.07/45.27             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 45.07/45.27             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 45.07/45.27          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27               (k1_zfmisc_1 @ 
% 45.07/45.27                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 45.07/45.27          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 45.07/45.27          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 45.07/45.27               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 45.07/45.27          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 45.07/45.27          | ~ (m1_pre_topc @ X0 @ sk_A)
% 45.07/45.27          | (v2_struct_0 @ X0)
% 45.07/45.27          | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('demod', [status(thm)], ['168', '239'])).
% 45.07/45.27  thf('241', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 45.07/45.27        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 45.07/45.27        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 45.07/45.27        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27             sk_B)
% 45.07/45.27        | (v5_pre_topc @ 
% 45.07/45.27           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 45.07/45.27           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 45.07/45.27        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('sup-', [status(thm)], ['124', '240'])).
% 45.07/45.27  thf('242', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('243', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['200', '206'])).
% 45.07/45.27  thf('244', plain,
% 45.07/45.27      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 45.07/45.27        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['191', '197'])).
% 45.07/45.27  thf('245', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 45.07/45.27         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 45.07/45.27               sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['186'])).
% 45.07/45.27  thf('246', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 45.07/45.27        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('247', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 45.07/45.27       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('split', [status(esa)], ['246'])).
% 45.07/45.27  thf('248', plain,
% 45.07/45.27      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['224', '235', '247'])).
% 45.07/45.27  thf('249', plain,
% 45.07/45.27      ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['245', '248'])).
% 45.07/45.27  thf('250', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('251', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('252', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('253', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('demod', [status(thm)],
% 45.07/45.27                ['241', '242', '243', '244', '249', '250', '251', '252'])).
% 45.07/45.27  thf('254', plain,
% 45.07/45.27      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_B))),
% 45.07/45.27      inference('sup+', [status(thm)], ['109', '253'])).
% 45.07/45.27  thf('255', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_B)
% 45.07/45.27        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('simplify', [status(thm)], ['254'])).
% 45.07/45.27  thf('256', plain,
% 45.07/45.27      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 45.07/45.27         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 45.07/45.27      inference('split', [status(esa)], ['42'])).
% 45.07/45.27  thf('257', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 45.07/45.27      inference('sat_resolution*', [status(thm)], ['224', '235'])).
% 45.07/45.27  thf('258', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 45.07/45.27      inference('simpl_trail', [status(thm)], ['256', '257'])).
% 45.07/45.27  thf('259', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_B)
% 45.07/45.27        | (v2_struct_0 @ sk_D)
% 45.07/45.27        | (v2_struct_0 @ sk_A)
% 45.07/45.27        | (v2_struct_0 @ sk_E))),
% 45.07/45.27      inference('sup-', [status(thm)], ['255', '258'])).
% 45.07/45.27  thf('260', plain, (~ (v2_struct_0 @ sk_B)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('261', plain,
% 45.07/45.27      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 45.07/45.27      inference('sup-', [status(thm)], ['259', '260'])).
% 45.07/45.27  thf('262', plain, (~ (v2_struct_0 @ sk_E)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('263', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 45.07/45.27      inference('clc', [status(thm)], ['261', '262'])).
% 45.07/45.27  thf('264', plain, (~ (v2_struct_0 @ sk_D)),
% 45.07/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.07/45.27  thf('265', plain, ((v2_struct_0 @ sk_A)),
% 45.07/45.27      inference('clc', [status(thm)], ['263', '264'])).
% 45.07/45.27  thf('266', plain, ($false), inference('demod', [status(thm)], ['0', '265'])).
% 45.07/45.27  
% 45.07/45.27  % SZS output end Refutation
% 45.07/45.27  
% 45.07/45.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
