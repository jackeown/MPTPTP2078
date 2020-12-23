%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0onnR6PSch

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:08 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  304 (1936 expanded)
%              Number of leaves         :   34 ( 556 expanded)
%              Depth                    :   28
%              Number of atoms          : 4153 (122779 expanded)
%              Number of equality atoms :   36 ( 806 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

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

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X17 @ X18 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8','11','12','13'])).

thf('15',plain,
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

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('24',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['25'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['2','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8','11','12','13'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('32',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','41'])).

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

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X28 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X28 ) @ X28 @ X24 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X25 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X25 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X25 ) @ X25 @ X24 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X26 @ X24 @ X27 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( r4_tsep_1 @ X26 @ X28 @ X25 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('44',plain,(
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
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v5_pre_topc @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X21 @ X22 @ X20 @ X23 ) @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
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

thf('71',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['2','26'])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X17 @ X18 @ X16 @ X19 ) @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('83',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('85',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['85'])).

thf('87',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['73','86'])).

thf('88',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X17 @ X18 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['15'])).

thf('99',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['22','23'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['101'])).

thf('103',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['89','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','41'])).

thf('105',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('108',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('109',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('111',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['111'])).

thf('113',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['106','112'])).

thf('114',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['15'])).

thf('118',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('120',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['120'])).

thf('122',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['115','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','87','103','104','113','122','123','124','125'])).

thf('127',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['69','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','127'])).

thf('129',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('139',plain,
    ( ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['148'])).

thf('150',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['136','147','149'])).

thf('151',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['52','150'])).

thf('152',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['106','112'])).

thf('153',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['115','121'])).

thf('154',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
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
    inference(demod,[status(thm)],['44','45','46','47','48','49','50','151','152','153','154','155'])).

thf('157',plain,
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
    inference('sup-',[status(thm)],['27','156'])).

thf('158',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['89','102'])).

thf('160',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['73','86'])).

thf('161',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['68'])).

thf('162',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['162'])).

thf('164',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['136','147','163'])).

thf('165',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['161','164'])).

thf('166',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','159','160','165','166','167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8','11','12','13'])).

thf('173',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['173'])).

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

thf('175',plain,(
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

thf('176',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        | ( sk_C = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        | ( sk_C = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('182',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['179','183'])).

thf('185',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','184'])).

thf('186',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('187',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('188',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('189',plain,(
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

thf('190',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ X31 @ ( k3_tmap_1 @ X33 @ X30 @ X32 @ X32 @ X31 ) )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('191',plain,(
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
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194','195'])).

thf('197',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['188','196'])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('200',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('201',plain,(
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

thf('202',plain,(
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

thf('203',plain,(
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
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
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
    inference(demod,[status(thm)],['203','204','205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','208'])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('218',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['173'])).

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

thf('219',plain,(
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

thf('220',plain,
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
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
          = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['220','221','222','223','224','225','226'])).

thf('228',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['182'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['227','228'])).

thf('230',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['217','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['215','216','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['197','198','241','242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','249'])).

thf('251',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','250'])).

thf('252',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('253',plain,
    ( ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','253'])).

thf('255',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('256',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','256'])).

thf('258',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('259',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['136','147'])).

thf('260',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['257','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    $false ),
    inference(demod,[status(thm)],['0','267'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0onnR6PSch
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 473 iterations in 0.330s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.80  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.80  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.58/0.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.58/0.80  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.80  thf(t132_tmap_1, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.80             ( l1_pre_topc @ B ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.80                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                 ( m1_subset_1 @
% 0.58/0.80                   C @ 
% 0.58/0.80                   ( k1_zfmisc_1 @
% 0.58/0.80                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.80               ( ![D:$i]:
% 0.58/0.80                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80                   ( ![E:$i]:
% 0.58/0.80                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.58/0.80                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.58/0.80                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.58/0.80                         ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.80                             ( v1_funct_2 @
% 0.58/0.80                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                             ( v5_pre_topc @ C @ A @ B ) & 
% 0.58/0.80                             ( m1_subset_1 @
% 0.58/0.80                               C @ 
% 0.58/0.80                               ( k1_zfmisc_1 @
% 0.58/0.80                                 ( k2_zfmisc_1 @
% 0.58/0.80                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.58/0.80                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.58/0.80                             ( v1_funct_2 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.58/0.80                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                             ( v5_pre_topc @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.58/0.80                             ( m1_subset_1 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.58/0.80                               ( k1_zfmisc_1 @
% 0.58/0.80                                 ( k2_zfmisc_1 @
% 0.58/0.80                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.58/0.80                             ( v1_funct_2 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.58/0.80                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                             ( v5_pre_topc @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.58/0.80                             ( m1_subset_1 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.58/0.80                               ( k1_zfmisc_1 @
% 0.58/0.80                                 ( k2_zfmisc_1 @
% 0.58/0.80                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80            ( l1_pre_topc @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.80                ( l1_pre_topc @ B ) ) =>
% 0.58/0.80              ( ![C:$i]:
% 0.58/0.80                ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.80                    ( v1_funct_2 @
% 0.58/0.80                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                    ( m1_subset_1 @
% 0.58/0.80                      C @ 
% 0.58/0.80                      ( k1_zfmisc_1 @
% 0.58/0.80                        ( k2_zfmisc_1 @
% 0.58/0.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.80                  ( ![D:$i]:
% 0.58/0.80                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80                      ( ![E:$i]:
% 0.58/0.80                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.58/0.80                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.58/0.80                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.58/0.80                            ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.80                                ( v1_funct_2 @
% 0.58/0.80                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                                ( v5_pre_topc @ C @ A @ B ) & 
% 0.58/0.80                                ( m1_subset_1 @
% 0.58/0.80                                  C @ 
% 0.58/0.80                                  ( k1_zfmisc_1 @
% 0.58/0.80                                    ( k2_zfmisc_1 @
% 0.58/0.80                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.58/0.80                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.58/0.80                                ( v1_funct_2 @
% 0.58/0.80                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.58/0.80                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                                ( v5_pre_topc @
% 0.58/0.80                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.58/0.80                                ( m1_subset_1 @
% 0.58/0.80                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.58/0.80                                  ( k1_zfmisc_1 @
% 0.58/0.80                                    ( k2_zfmisc_1 @
% 0.58/0.80                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.58/0.80                                ( v1_funct_2 @
% 0.58/0.80                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.58/0.80                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                                ( v5_pre_topc @
% 0.58/0.80                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.58/0.80                                ( m1_subset_1 @
% 0.58/0.80                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.58/0.80                                  ( k1_zfmisc_1 @
% 0.58/0.80                                    ( k2_zfmisc_1 @
% 0.58/0.80                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 0.58/0.80  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80        | (v1_funct_1 @ sk_C))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.58/0.80         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.58/0.80      inference('split', [status(esa)], ['1'])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_k2_tmap_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.58/0.80         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80         ( m1_subset_1 @
% 0.58/0.80           C @ 
% 0.58/0.80           ( k1_zfmisc_1 @
% 0.58/0.80             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80         ( l1_struct_0 @ D ) ) =>
% 0.58/0.80       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.58/0.80         ( v1_funct_2 @
% 0.58/0.80           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.58/0.80           ( u1_struct_0 @ B ) ) & 
% 0.58/0.80         ( m1_subset_1 @
% 0.58/0.80           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.58/0.80           ( k1_zfmisc_1 @
% 0.58/0.80             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X16 @ 
% 0.58/0.80             (k1_zfmisc_1 @ 
% 0.58/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))))
% 0.58/0.80          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.58/0.80          | ~ (v1_funct_1 @ X16)
% 0.58/0.80          | ~ (l1_struct_0 @ X18)
% 0.58/0.80          | ~ (l1_struct_0 @ X17)
% 0.58/0.80          | ~ (l1_struct_0 @ X19)
% 0.58/0.80          | (m1_subset_1 @ (k2_tmap_1 @ X17 @ X18 @ X16 @ X19) @ 
% 0.58/0.80             (k1_zfmisc_1 @ 
% 0.58/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18)))))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80          | ~ (l1_struct_0 @ X0)
% 0.58/0.80          | ~ (l1_struct_0 @ sk_A)
% 0.58/0.80          | ~ (l1_struct_0 @ sk_B)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_C)
% 0.58/0.80          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.80  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_l1_pre_topc, axiom,
% 0.58/0.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.80  thf('7', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.80  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.80  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('10', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.80  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.80  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80          | ~ (l1_struct_0 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['5', '8', '11', '12', '13'])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.58/0.80             sk_B)
% 0.58/0.80        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.58/0.80        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.58/0.80        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80             (k1_zfmisc_1 @ 
% 0.58/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.58/0.80             sk_B)
% 0.58/0.80        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.80        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.58/0.80        | ~ (m1_subset_1 @ sk_C @ 
% 0.58/0.80             (k1_zfmisc_1 @ 
% 0.58/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.58/0.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.80        | ~ (v1_funct_1 @ sk_C))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.58/0.80      inference('split', [status(esa)], ['15'])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      ((~ (l1_struct_0 @ sk_E))
% 0.58/0.80         <= (~
% 0.58/0.80             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['14', '16'])).
% 0.58/0.80  thf('18', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_m1_pre_topc, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) =>
% 0.58/0.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.80  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 0.58/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('22', plain, ((l1_pre_topc @ sk_E)),
% 0.58/0.80      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.80  thf('23', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.80  thf('24', plain, ((l1_struct_0 @ sk_E)),
% 0.58/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['17', '24'])).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['25'])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['2', '26'])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80        | (v1_funct_1 @ sk_C))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.58/0.80         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.58/0.80      inference('split', [status(esa)], ['28'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80          | ~ (l1_struct_0 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['5', '8', '11', '12', '13'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80           (k1_zfmisc_1 @ 
% 0.58/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.58/0.80         <= (~
% 0.58/0.80             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.58/0.80      inference('split', [status(esa)], ['15'])).
% 0.58/0.80  thf('32', plain,
% 0.58/0.80      ((~ (l1_struct_0 @ sk_D))
% 0.58/0.80         <= (~
% 0.58/0.80             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.80  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.80  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.58/0.80      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.80  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('37', plain, ((l1_pre_topc @ sk_D)),
% 0.58/0.80      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.80  thf('38', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.80  thf('39', plain, ((l1_struct_0 @ sk_D)),
% 0.58/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['32', '39'])).
% 0.58/0.80  thf('41', plain,
% 0.58/0.80      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80         (k1_zfmisc_1 @ 
% 0.58/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['40'])).
% 0.58/0.80  thf('42', plain,
% 0.58/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('simpl_trail', [status(thm)], ['29', '41'])).
% 0.58/0.80  thf(t129_tmap_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.80             ( l1_pre_topc @ B ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80               ( ![D:$i]:
% 0.58/0.80                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.58/0.80                     ( ![E:$i]:
% 0.58/0.80                       ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.80                           ( v1_funct_2 @
% 0.58/0.80                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                           ( m1_subset_1 @
% 0.58/0.80                             E @ 
% 0.58/0.80                             ( k1_zfmisc_1 @
% 0.58/0.80                               ( k2_zfmisc_1 @
% 0.58/0.80                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.80                         ( ( ( v1_funct_1 @
% 0.58/0.80                               ( k2_tmap_1 @
% 0.58/0.80                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 0.58/0.80                             ( v1_funct_2 @
% 0.58/0.80                               ( k2_tmap_1 @
% 0.58/0.80                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.58/0.80                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.58/0.80                               ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                             ( v5_pre_topc @
% 0.58/0.80                               ( k2_tmap_1 @
% 0.58/0.80                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.58/0.80                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.58/0.80                             ( m1_subset_1 @
% 0.58/0.80                               ( k2_tmap_1 @
% 0.58/0.80                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.58/0.80                               ( k1_zfmisc_1 @
% 0.58/0.80                                 ( k2_zfmisc_1 @
% 0.58/0.80                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.58/0.80                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.58/0.80                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.58/0.80                             ( v1_funct_2 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 0.58/0.80                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                             ( v5_pre_topc @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 0.58/0.80                             ( m1_subset_1 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 0.58/0.80                               ( k1_zfmisc_1 @
% 0.58/0.80                                 ( k2_zfmisc_1 @
% 0.58/0.80                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 0.58/0.80                             ( v1_funct_2 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.58/0.80                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80                             ( v5_pre_topc @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 0.58/0.80                             ( m1_subset_1 @
% 0.58/0.80                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.58/0.80                               ( k1_zfmisc_1 @
% 0.58/0.80                                 ( k2_zfmisc_1 @
% 0.58/0.80                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X24)
% 0.58/0.80          | ~ (v2_pre_topc @ X24)
% 0.58/0.80          | ~ (l1_pre_topc @ X24)
% 0.58/0.80          | (v2_struct_0 @ X25)
% 0.58/0.80          | ~ (m1_pre_topc @ X25 @ X26)
% 0.58/0.80          | ~ (v1_funct_1 @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X28))
% 0.58/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X28) @ 
% 0.58/0.80               (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))
% 0.58/0.80          | ~ (v5_pre_topc @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X28) @ X28 @ X24)
% 0.58/0.80          | ~ (m1_subset_1 @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X28) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))))
% 0.58/0.80          | ~ (v1_funct_1 @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X25))
% 0.58/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X25) @ 
% 0.58/0.80               (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.58/0.80          | ~ (v5_pre_topc @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X25) @ X25 @ X24)
% 0.58/0.80          | ~ (m1_subset_1 @ (k2_tmap_1 @ X26 @ X24 @ X27 @ X25) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.58/0.80          | (v5_pre_topc @ 
% 0.58/0.80             (k2_tmap_1 @ X26 @ X24 @ X27 @ (k1_tsep_1 @ X26 @ X28 @ X25)) @ 
% 0.58/0.80             (k1_tsep_1 @ X26 @ X28 @ X25) @ X24)
% 0.58/0.80          | ~ (m1_subset_1 @ X27 @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))))
% 0.58/0.80          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))
% 0.58/0.80          | ~ (v1_funct_1 @ X27)
% 0.58/0.80          | ~ (r4_tsep_1 @ X26 @ X28 @ X25)
% 0.58/0.80          | ~ (m1_pre_topc @ X28 @ X26)
% 0.58/0.80          | (v2_struct_0 @ X28)
% 0.58/0.80          | ~ (l1_pre_topc @ X26)
% 0.58/0.80          | ~ (v2_pre_topc @ X26)
% 0.58/0.80          | (v2_struct_0 @ X26))),
% 0.58/0.80      inference('cnf', [status(esa)], [t129_tmap_1])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v2_struct_0 @ sk_A)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_D)
% 0.58/0.80          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.58/0.80          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_C)
% 0.58/0.80          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.80          | ~ (m1_subset_1 @ sk_C @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80          | (v5_pre_topc @ 
% 0.58/0.80             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.58/0.80             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 0.58/0.80          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.58/0.80               (k1_zfmisc_1 @ 
% 0.58/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.80          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.58/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.58/0.80               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.80          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.58/0.80          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.58/0.80               sk_B)
% 0.58/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.80               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.80          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.58/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ X0)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.80          | (v2_struct_0 @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.80  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.58/0.80        | (v1_funct_1 @ sk_C))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.58/0.80         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.58/0.80               sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['51'])).
% 0.58/0.80  thf('53', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('54', plain,
% 0.58/0.80      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.58/0.80        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.58/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['54'])).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      ((m1_subset_1 @ sk_C @ 
% 0.58/0.80        (k1_zfmisc_1 @ 
% 0.58/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(fc2_tmap_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.58/0.80         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( v1_funct_1 @ C ) & 
% 0.58/0.80         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.80         ( v5_pre_topc @ C @ A @ B ) & 
% 0.58/0.80         ( m1_subset_1 @
% 0.58/0.80           C @ 
% 0.58/0.80           ( k1_zfmisc_1 @
% 0.58/0.80             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.58/0.80         ( v1_funct_2 @
% 0.58/0.80           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.58/0.80           ( u1_struct_0 @ B ) ) & 
% 0.58/0.80         ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ))).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X20 @ 
% 0.58/0.80             (k1_zfmisc_1 @ 
% 0.58/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))))
% 0.58/0.80          | ~ (v5_pre_topc @ X20 @ X21 @ X22)
% 0.58/0.80          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.58/0.80          | ~ (v1_funct_1 @ X20)
% 0.58/0.80          | ~ (l1_pre_topc @ X22)
% 0.58/0.80          | ~ (v2_pre_topc @ X22)
% 0.58/0.80          | (v2_struct_0 @ X22)
% 0.58/0.80          | ~ (l1_pre_topc @ X21)
% 0.58/0.80          | ~ (v2_pre_topc @ X21)
% 0.58/0.80          | (v2_struct_0 @ X21)
% 0.58/0.80          | (v2_struct_0 @ X23)
% 0.58/0.80          | ~ (m1_pre_topc @ X23 @ X21)
% 0.58/0.80          | (v5_pre_topc @ (k2_tmap_1 @ X21 @ X22 @ X20 @ X23) @ X23 @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.58/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ X0)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_B)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.80          | ~ (v1_funct_1 @ sk_C)
% 0.58/0.80          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.80          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.80  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('64', plain,
% 0.63/0.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('65', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.63/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.80          | (v2_struct_0 @ X0)
% 0.63/0.80          | (v2_struct_0 @ sk_A)
% 0.63/0.80          | (v2_struct_0 @ sk_B)
% 0.63/0.80          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.80      inference('demod', [status(thm)],
% 0.63/0.80                ['58', '59', '60', '61', '62', '63', '64'])).
% 0.63/0.80  thf('66', plain,
% 0.63/0.80      ((![X0 : $i]:
% 0.63/0.80          ((v2_struct_0 @ sk_B)
% 0.63/0.80           | (v2_struct_0 @ sk_A)
% 0.63/0.80           | (v2_struct_0 @ X0)
% 0.63/0.80           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.80           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['55', '65'])).
% 0.63/0.80  thf('67', plain,
% 0.63/0.80      ((((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.63/0.80         | (v2_struct_0 @ sk_D)
% 0.63/0.80         | (v2_struct_0 @ sk_A)
% 0.63/0.80         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['53', '66'])).
% 0.63/0.80  thf('68', plain,
% 0.63/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.63/0.80        | (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('69', plain,
% 0.63/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.63/0.80         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('split', [status(esa)], ['68'])).
% 0.63/0.80  thf('70', plain,
% 0.63/0.80      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80           (k1_zfmisc_1 @ 
% 0.63/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.63/0.80        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80             sk_B)
% 0.63/0.80        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.63/0.80        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.63/0.80        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80             (k1_zfmisc_1 @ 
% 0.63/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.63/0.80        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.63/0.80             sk_B)
% 0.63/0.80        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.63/0.80        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.63/0.80        | ~ (m1_subset_1 @ sk_C @ 
% 0.63/0.80             (k1_zfmisc_1 @ 
% 0.63/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.63/0.80        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.63/0.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.80        | ~ (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('71', plain,
% 0.63/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80        (k1_zfmisc_1 @ 
% 0.63/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['2', '26'])).
% 0.63/0.80  thf('72', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.63/0.80        | (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('73', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.63/0.80         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('split', [status(esa)], ['72'])).
% 0.63/0.80  thf('74', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ 
% 0.63/0.80        (k1_zfmisc_1 @ 
% 0.63/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('75', plain,
% 0.63/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.63/0.80         (~ (m1_subset_1 @ X16 @ 
% 0.63/0.80             (k1_zfmisc_1 @ 
% 0.63/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))))
% 0.63/0.80          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.63/0.80          | ~ (v1_funct_1 @ X16)
% 0.63/0.80          | ~ (l1_struct_0 @ X18)
% 0.63/0.80          | ~ (l1_struct_0 @ X17)
% 0.63/0.80          | ~ (l1_struct_0 @ X19)
% 0.63/0.80          | (v1_funct_2 @ (k2_tmap_1 @ X17 @ X18 @ X16 @ X19) @ 
% 0.63/0.80             (u1_struct_0 @ X19) @ (u1_struct_0 @ X18)))),
% 0.63/0.80      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.63/0.80  thf('76', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.80           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.63/0.80          | ~ (l1_struct_0 @ X0)
% 0.63/0.80          | ~ (l1_struct_0 @ sk_A)
% 0.63/0.80          | ~ (l1_struct_0 @ sk_B)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['74', '75'])).
% 0.63/0.80  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.63/0.80  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.63/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.80  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('80', plain,
% 0.63/0.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('81', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.80           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.63/0.80          | ~ (l1_struct_0 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.63/0.80  thf('82', plain,
% 0.63/0.80      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('split', [status(esa)], ['15'])).
% 0.63/0.80  thf('83', plain,
% 0.63/0.80      ((~ (l1_struct_0 @ sk_E))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['81', '82'])).
% 0.63/0.80  thf('84', plain, ((l1_struct_0 @ sk_E)),
% 0.63/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.63/0.80  thf('85', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.63/0.80      inference('demod', [status(thm)], ['83', '84'])).
% 0.63/0.80  thf('86', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['85'])).
% 0.63/0.80  thf('87', plain,
% 0.63/0.80      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.80        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['73', '86'])).
% 0.63/0.80  thf('88', plain,
% 0.63/0.80      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.63/0.80        | (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('89', plain,
% 0.63/0.80      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.63/0.80         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.63/0.80      inference('split', [status(esa)], ['88'])).
% 0.63/0.80  thf('90', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ 
% 0.63/0.80        (k1_zfmisc_1 @ 
% 0.63/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('91', plain,
% 0.63/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.63/0.80         (~ (m1_subset_1 @ X16 @ 
% 0.63/0.80             (k1_zfmisc_1 @ 
% 0.63/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))))
% 0.63/0.80          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.63/0.80          | ~ (v1_funct_1 @ X16)
% 0.63/0.80          | ~ (l1_struct_0 @ X18)
% 0.63/0.80          | ~ (l1_struct_0 @ X17)
% 0.63/0.80          | ~ (l1_struct_0 @ X19)
% 0.63/0.80          | (v1_funct_1 @ (k2_tmap_1 @ X17 @ X18 @ X16 @ X19)))),
% 0.63/0.80      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.63/0.80  thf('92', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.63/0.80          | ~ (l1_struct_0 @ X0)
% 0.63/0.80          | ~ (l1_struct_0 @ sk_A)
% 0.63/0.80          | ~ (l1_struct_0 @ sk_B)
% 0.63/0.80          | ~ (v1_funct_1 @ sk_C)
% 0.63/0.80          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['90', '91'])).
% 0.63/0.80  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.63/0.80  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.63/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.80  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('96', plain,
% 0.63/0.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('97', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.63/0.80          | ~ (l1_struct_0 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.63/0.80  thf('98', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.63/0.80         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.63/0.80      inference('split', [status(esa)], ['15'])).
% 0.63/0.80  thf('99', plain,
% 0.63/0.80      ((~ (l1_struct_0 @ sk_E))
% 0.63/0.80         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['97', '98'])).
% 0.63/0.80  thf('100', plain, ((l1_struct_0 @ sk_E)),
% 0.63/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.63/0.80  thf('101', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.63/0.80      inference('demod', [status(thm)], ['99', '100'])).
% 0.63/0.80  thf('102', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['101'])).
% 0.63/0.80  thf('103', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['89', '102'])).
% 0.63/0.80  thf('104', plain,
% 0.63/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80        (k1_zfmisc_1 @ 
% 0.63/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['29', '41'])).
% 0.63/0.80  thf('105', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.63/0.80        | (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('106', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.63/0.80         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('split', [status(esa)], ['105'])).
% 0.63/0.80  thf('107', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.80           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.63/0.80          | ~ (l1_struct_0 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.63/0.80  thf('108', plain,
% 0.63/0.80      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('split', [status(esa)], ['15'])).
% 0.63/0.80  thf('109', plain,
% 0.63/0.80      ((~ (l1_struct_0 @ sk_D))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['107', '108'])).
% 0.63/0.80  thf('110', plain, ((l1_struct_0 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('111', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.63/0.80      inference('demod', [status(thm)], ['109', '110'])).
% 0.63/0.80  thf('112', plain,
% 0.63/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['111'])).
% 0.63/0.80  thf('113', plain,
% 0.63/0.80      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['106', '112'])).
% 0.63/0.80  thf('114', plain,
% 0.63/0.80      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.63/0.80        | (v1_funct_1 @ sk_C))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('115', plain,
% 0.63/0.80      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.63/0.80         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.63/0.80      inference('split', [status(esa)], ['114'])).
% 0.63/0.80  thf('116', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.63/0.80          | ~ (l1_struct_0 @ X0))),
% 0.63/0.80      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.63/0.80  thf('117', plain,
% 0.63/0.80      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.63/0.80         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.63/0.80      inference('split', [status(esa)], ['15'])).
% 0.63/0.80  thf('118', plain,
% 0.63/0.80      ((~ (l1_struct_0 @ sk_D))
% 0.63/0.80         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['116', '117'])).
% 0.63/0.80  thf('119', plain, ((l1_struct_0 @ sk_D)),
% 0.63/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.63/0.80  thf('120', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.63/0.80      inference('demod', [status(thm)], ['118', '119'])).
% 0.63/0.80  thf('121', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['120'])).
% 0.63/0.80  thf('122', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['115', '121'])).
% 0.63/0.80  thf('123', plain,
% 0.63/0.80      ((m1_subset_1 @ sk_C @ 
% 0.63/0.80        (k1_zfmisc_1 @ 
% 0.63/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('124', plain,
% 0.63/0.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('126', plain,
% 0.63/0.80      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.63/0.80        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.63/0.80             sk_B)
% 0.63/0.80        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.80      inference('demod', [status(thm)],
% 0.63/0.80                ['70', '71', '87', '103', '104', '113', '122', '123', '124', 
% 0.63/0.80                 '125'])).
% 0.63/0.80  thf('127', plain,
% 0.63/0.80      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.63/0.80         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.63/0.80              sk_B)))
% 0.63/0.80         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['69', '126'])).
% 0.63/0.80  thf('128', plain,
% 0.63/0.80      ((((v2_struct_0 @ sk_B)
% 0.63/0.80         | (v2_struct_0 @ sk_A)
% 0.63/0.80         | (v2_struct_0 @ sk_D)
% 0.63/0.80         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['67', '127'])).
% 0.63/0.80  thf('129', plain,
% 0.63/0.80      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('split', [status(esa)], ['54'])).
% 0.63/0.80  thf('130', plain,
% 0.63/0.80      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('demod', [status(thm)], ['128', '129'])).
% 0.63/0.80  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('132', plain,
% 0.63/0.80      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('clc', [status(thm)], ['130', '131'])).
% 0.63/0.80  thf('133', plain, (~ (v2_struct_0 @ sk_D)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('134', plain,
% 0.63/0.80      (((v2_struct_0 @ sk_A))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('clc', [status(thm)], ['132', '133'])).
% 0.63/0.80  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('136', plain,
% 0.63/0.80      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.63/0.80       ~
% 0.63/0.80       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 0.63/0.80      inference('sup-', [status(thm)], ['134', '135'])).
% 0.63/0.80  thf('137', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('138', plain,
% 0.63/0.80      ((![X0 : $i]:
% 0.63/0.80          ((v2_struct_0 @ sk_B)
% 0.63/0.80           | (v2_struct_0 @ sk_A)
% 0.63/0.80           | (v2_struct_0 @ X0)
% 0.63/0.80           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.80           | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)))
% 0.63/0.80         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['55', '65'])).
% 0.63/0.80  thf('139', plain,
% 0.63/0.80      ((((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.63/0.80         | (v2_struct_0 @ sk_E)
% 0.63/0.80         | (v2_struct_0 @ sk_A)
% 0.63/0.80         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['137', '138'])).
% 0.63/0.80  thf('140', plain,
% 0.63/0.80      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)))),
% 0.63/0.80      inference('split', [status(esa)], ['15'])).
% 0.63/0.80  thf('141', plain,
% 0.63/0.80      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['139', '140'])).
% 0.63/0.80  thf('142', plain, (~ (v2_struct_0 @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('143', plain,
% 0.63/0.80      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('clc', [status(thm)], ['141', '142'])).
% 0.63/0.80  thf('144', plain, (~ (v2_struct_0 @ sk_E)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('145', plain,
% 0.63/0.80      (((v2_struct_0 @ sk_A))
% 0.63/0.80         <= (~
% 0.63/0.80             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.80               sk_B)) & 
% 0.63/0.80             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.80      inference('clc', [status(thm)], ['143', '144'])).
% 0.63/0.80  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('147', plain,
% 0.63/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.63/0.80       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.80      inference('sup-', [status(thm)], ['145', '146'])).
% 0.63/0.80  thf('148', plain,
% 0.63/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.63/0.80        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('149', plain,
% 0.63/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.63/0.80       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.80      inference('split', [status(esa)], ['148'])).
% 0.63/0.80  thf('150', plain,
% 0.63/0.80      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['136', '147', '149'])).
% 0.63/0.80  thf('151', plain,
% 0.63/0.80      ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['52', '150'])).
% 0.63/0.80  thf('152', plain,
% 0.63/0.80      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.63/0.80        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['106', '112'])).
% 0.63/0.80  thf('153', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['115', '121'])).
% 0.63/0.80  thf('154', plain, ((l1_pre_topc @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('155', plain, ((v2_pre_topc @ sk_B)),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('156', plain,
% 0.63/0.80      (![X0 : $i]:
% 0.63/0.80         ((v2_struct_0 @ sk_A)
% 0.63/0.80          | (v2_struct_0 @ sk_D)
% 0.63/0.80          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.63/0.80          | (v5_pre_topc @ 
% 0.63/0.80             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.63/0.80             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 0.63/0.80          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.80               (k1_zfmisc_1 @ 
% 0.63/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.63/0.80          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 0.63/0.81          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.81               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.63/0.81          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | (v2_struct_0 @ X0)
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('demod', [status(thm)],
% 0.63/0.81                ['44', '45', '46', '47', '48', '49', '50', '151', '152', 
% 0.63/0.81                 '153', '154', '155'])).
% 0.63/0.81  thf('157', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | (v2_struct_0 @ sk_E)
% 0.63/0.81        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.63/0.81        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.63/0.81        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.81             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.63/0.81        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.81             sk_B)
% 0.63/0.81        | (v5_pre_topc @ 
% 0.63/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.63/0.81           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 0.63/0.81        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.63/0.81        | (v2_struct_0 @ sk_D)
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('sup-', [status(thm)], ['27', '156'])).
% 0.63/0.81  thf('158', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('159', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.63/0.81      inference('simpl_trail', [status(thm)], ['89', '102'])).
% 0.63/0.81  thf('160', plain,
% 0.63/0.81      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.63/0.81        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.63/0.81      inference('simpl_trail', [status(thm)], ['73', '86'])).
% 0.63/0.81  thf('161', plain,
% 0.63/0.81      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.63/0.81         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.63/0.81               sk_B)))),
% 0.63/0.81      inference('split', [status(esa)], ['68'])).
% 0.63/0.81  thf('162', plain,
% 0.63/0.81      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.63/0.81        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('163', plain,
% 0.63/0.81      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.63/0.81       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.81      inference('split', [status(esa)], ['162'])).
% 0.63/0.81  thf('164', plain,
% 0.63/0.81      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 0.63/0.81      inference('sat_resolution*', [status(thm)], ['136', '147', '163'])).
% 0.63/0.81  thf('165', plain,
% 0.63/0.81      ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)),
% 0.63/0.81      inference('simpl_trail', [status(thm)], ['161', '164'])).
% 0.63/0.81  thf('166', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('167', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('168', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('169', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | (v2_struct_0 @ sk_E)
% 0.63/0.81        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ sk_B)
% 0.63/0.81        | (v2_struct_0 @ sk_D)
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)],
% 0.63/0.81                ['157', '158', '159', '160', '165', '166', '167', '168'])).
% 0.63/0.81  thf('170', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.63/0.81          | ~ (l1_struct_0 @ X0))),
% 0.63/0.81      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.63/0.81  thf('171', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.81           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.63/0.81          | ~ (l1_struct_0 @ X0))),
% 0.63/0.81      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.63/0.81  thf('172', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.63/0.81           (k1_zfmisc_1 @ 
% 0.63/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.63/0.81          | ~ (l1_struct_0 @ X0))),
% 0.63/0.81      inference('demod', [status(thm)], ['5', '8', '11', '12', '13'])).
% 0.63/0.81  thf('173', plain,
% 0.63/0.81      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.63/0.81        | (m1_subset_1 @ sk_C @ 
% 0.63/0.81           (k1_zfmisc_1 @ 
% 0.63/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('174', plain,
% 0.63/0.81      (((m1_subset_1 @ sk_C @ 
% 0.63/0.81         (k1_zfmisc_1 @ 
% 0.63/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.63/0.81         <= (((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('split', [status(esa)], ['173'])).
% 0.63/0.81  thf(redefinition_r2_funct_2, axiom,
% 0.63/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.63/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.63/0.81         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.63/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.63/0.81       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.63/0.81  thf('175', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.63/0.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.63/0.81          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.63/0.81          | ~ (v1_funct_1 @ X0)
% 0.63/0.81          | ~ (v1_funct_1 @ X3)
% 0.63/0.81          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.63/0.81          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.63/0.81          | ((X0) = (X3))
% 0.63/0.81          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.63/0.81      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.63/0.81  thf('176', plain,
% 0.63/0.81      ((![X0 : $i]:
% 0.63/0.81          (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81              sk_C @ X0)
% 0.63/0.81           | ((sk_C) = (X0))
% 0.63/0.81           | ~ (m1_subset_1 @ X0 @ 
% 0.63/0.81                (k1_zfmisc_1 @ 
% 0.63/0.81                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.63/0.81           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81           | ~ (v1_funct_1 @ X0)
% 0.63/0.81           | ~ (v1_funct_1 @ sk_C)
% 0.63/0.81           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.63/0.81         <= (((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['174', '175'])).
% 0.63/0.81  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('178', plain,
% 0.63/0.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('179', plain,
% 0.63/0.81      ((![X0 : $i]:
% 0.63/0.81          (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81              sk_C @ X0)
% 0.63/0.81           | ((sk_C) = (X0))
% 0.63/0.81           | ~ (m1_subset_1 @ X0 @ 
% 0.63/0.81                (k1_zfmisc_1 @ 
% 0.63/0.81                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.63/0.81           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81           | ~ (v1_funct_1 @ X0)))
% 0.63/0.81         <= (((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.63/0.81  thf('180', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ 
% 0.63/0.81        (k1_zfmisc_1 @ 
% 0.63/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('181', plain,
% 0.63/0.81      ((~ (m1_subset_1 @ sk_C @ 
% 0.63/0.81           (k1_zfmisc_1 @ 
% 0.63/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.63/0.81         <= (~
% 0.63/0.81             ((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('split', [status(esa)], ['15'])).
% 0.63/0.81  thf('182', plain,
% 0.63/0.81      (((m1_subset_1 @ sk_C @ 
% 0.63/0.81         (k1_zfmisc_1 @ 
% 0.63/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['180', '181'])).
% 0.63/0.81  thf('183', plain,
% 0.63/0.81      (((m1_subset_1 @ sk_C @ 
% 0.63/0.81         (k1_zfmisc_1 @ 
% 0.63/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.63/0.81      inference('sat_resolution*', [status(thm)], ['182'])).
% 0.63/0.81  thf('184', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81             X0)
% 0.63/0.81          | ((sk_C) = (X0))
% 0.63/0.81          | ~ (m1_subset_1 @ X0 @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.63/0.81          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81          | ~ (v1_funct_1 @ X0))),
% 0.63/0.81      inference('simpl_trail', [status(thm)], ['179', '183'])).
% 0.63/0.81  thf('185', plain,
% 0.63/0.81      ((~ (l1_struct_0 @ sk_A)
% 0.63/0.81        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.63/0.81             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['172', '184'])).
% 0.63/0.81  thf('186', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.63/0.81  thf('187', plain,
% 0.63/0.81      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.63/0.81             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('demod', [status(thm)], ['185', '186'])).
% 0.63/0.81  thf(t2_tsep_1, axiom,
% 0.63/0.81    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.63/0.81  thf('188', plain,
% 0.63/0.81      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.63/0.81      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.63/0.81  thf('189', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ 
% 0.63/0.81        (k1_zfmisc_1 @ 
% 0.63/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(t74_tmap_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.81       ( ![B:$i]:
% 0.63/0.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.63/0.81             ( l1_pre_topc @ B ) ) =>
% 0.63/0.81           ( ![C:$i]:
% 0.63/0.81             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.63/0.81               ( ![D:$i]:
% 0.63/0.81                 ( ( ( v1_funct_1 @ D ) & 
% 0.63/0.81                     ( v1_funct_2 @
% 0.63/0.81                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.63/0.81                     ( m1_subset_1 @
% 0.63/0.81                       D @ 
% 0.63/0.81                       ( k1_zfmisc_1 @
% 0.63/0.81                         ( k2_zfmisc_1 @
% 0.63/0.81                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.63/0.81                   ( r2_funct_2 @
% 0.63/0.81                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.63/0.81                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.63/0.81  thf('190', plain,
% 0.63/0.81      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X30)
% 0.63/0.81          | ~ (v2_pre_topc @ X30)
% 0.63/0.81          | ~ (l1_pre_topc @ X30)
% 0.63/0.81          | ~ (v1_funct_1 @ X31)
% 0.63/0.81          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 0.63/0.81          | ~ (m1_subset_1 @ X31 @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 0.63/0.81          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ X31 @ 
% 0.63/0.81             (k3_tmap_1 @ X33 @ X30 @ X32 @ X32 @ X31))
% 0.63/0.81          | ~ (m1_pre_topc @ X32 @ X33)
% 0.63/0.81          | (v2_struct_0 @ X32)
% 0.63/0.81          | ~ (l1_pre_topc @ X33)
% 0.63/0.81          | ~ (v2_pre_topc @ X33)
% 0.63/0.81          | (v2_struct_0 @ X33))),
% 0.63/0.81      inference('cnf', [status(esa)], [t74_tmap_1])).
% 0.63/0.81  thf('191', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X0)
% 0.63/0.81          | ~ (v2_pre_topc @ X0)
% 0.63/0.81          | ~ (l1_pre_topc @ X0)
% 0.63/0.81          | (v2_struct_0 @ sk_A)
% 0.63/0.81          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.63/0.81          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C))
% 0.63/0.81          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81          | ~ (v1_funct_1 @ sk_C)
% 0.63/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.63/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('sup-', [status(thm)], ['189', '190'])).
% 0.63/0.81  thf('192', plain,
% 0.63/0.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('194', plain, ((l1_pre_topc @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('195', plain, ((v2_pre_topc @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('196', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X0)
% 0.63/0.81          | ~ (v2_pre_topc @ X0)
% 0.63/0.81          | ~ (l1_pre_topc @ X0)
% 0.63/0.81          | (v2_struct_0 @ sk_A)
% 0.63/0.81          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.63/0.81          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C))
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['191', '192', '193', '194', '195'])).
% 0.63/0.81  thf('197', plain,
% 0.63/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.81        | (v2_struct_0 @ sk_B)
% 0.63/0.81        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C))
% 0.63/0.81        | (v2_struct_0 @ sk_A)
% 0.63/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.63/0.81        | ~ (v2_pre_topc @ sk_A)
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('sup-', [status(thm)], ['188', '196'])).
% 0.63/0.81  thf('198', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('199', plain,
% 0.63/0.81      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.63/0.81      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.63/0.81  thf('200', plain,
% 0.63/0.81      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.63/0.81      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.63/0.81  thf('201', plain,
% 0.63/0.81      ((m1_subset_1 @ sk_C @ 
% 0.63/0.81        (k1_zfmisc_1 @ 
% 0.63/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf(d5_tmap_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.81       ( ![B:$i]:
% 0.63/0.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.63/0.81             ( l1_pre_topc @ B ) ) =>
% 0.63/0.81           ( ![C:$i]:
% 0.63/0.81             ( ( m1_pre_topc @ C @ A ) =>
% 0.63/0.81               ( ![D:$i]:
% 0.63/0.81                 ( ( m1_pre_topc @ D @ A ) =>
% 0.63/0.81                   ( ![E:$i]:
% 0.63/0.81                     ( ( ( v1_funct_1 @ E ) & 
% 0.63/0.81                         ( v1_funct_2 @
% 0.63/0.81                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.63/0.81                         ( m1_subset_1 @
% 0.63/0.81                           E @ 
% 0.63/0.81                           ( k1_zfmisc_1 @
% 0.63/0.81                             ( k2_zfmisc_1 @
% 0.63/0.81                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.63/0.81                       ( ( m1_pre_topc @ D @ C ) =>
% 0.63/0.81                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.63/0.81                           ( k2_partfun1 @
% 0.63/0.81                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.63/0.81                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.63/0.81  thf('202', plain,
% 0.63/0.81      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X11)
% 0.63/0.81          | ~ (v2_pre_topc @ X11)
% 0.63/0.81          | ~ (l1_pre_topc @ X11)
% 0.63/0.81          | ~ (m1_pre_topc @ X12 @ X13)
% 0.63/0.81          | ~ (m1_pre_topc @ X12 @ X14)
% 0.63/0.81          | ((k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11) @ 
% 0.63/0.81                 X15 @ (u1_struct_0 @ X12)))
% 0.63/0.81          | ~ (m1_subset_1 @ X15 @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))))
% 0.63/0.81          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))
% 0.63/0.81          | ~ (v1_funct_1 @ X15)
% 0.63/0.81          | ~ (m1_pre_topc @ X14 @ X13)
% 0.63/0.81          | ~ (l1_pre_topc @ X13)
% 0.63/0.81          | ~ (v2_pre_topc @ X13)
% 0.63/0.81          | (v2_struct_0 @ X13))),
% 0.63/0.81      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.63/0.81  thf('203', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X0)
% 0.63/0.81          | ~ (v2_pre_topc @ X0)
% 0.63/0.81          | ~ (l1_pre_topc @ X0)
% 0.63/0.81          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.63/0.81          | ~ (v1_funct_1 @ sk_C)
% 0.63/0.81          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                 sk_C @ (u1_struct_0 @ X1)))
% 0.63/0.81          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.63/0.81          | ~ (m1_pre_topc @ X1 @ X0)
% 0.63/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.63/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('sup-', [status(thm)], ['201', '202'])).
% 0.63/0.81  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('205', plain,
% 0.63/0.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('206', plain, ((l1_pre_topc @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('207', plain, ((v2_pre_topc @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('208', plain,
% 0.63/0.81      (![X0 : $i, X1 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X0)
% 0.63/0.81          | ~ (v2_pre_topc @ X0)
% 0.63/0.81          | ~ (l1_pre_topc @ X0)
% 0.63/0.81          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.63/0.81          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                 sk_C @ (u1_struct_0 @ X1)))
% 0.63/0.81          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.63/0.81          | ~ (m1_pre_topc @ X1 @ X0)
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('demod', [status(thm)], ['203', '204', '205', '206', '207'])).
% 0.63/0.81  thf('209', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         (~ (l1_pre_topc @ sk_A)
% 0.63/0.81          | (v2_struct_0 @ sk_B)
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                 sk_C @ (u1_struct_0 @ X0)))
% 0.63/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.63/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.63/0.81          | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('sup-', [status(thm)], ['200', '208'])).
% 0.63/0.81  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('211', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('213', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v2_struct_0 @ sk_B)
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                 sk_C @ (u1_struct_0 @ X0)))
% 0.63/0.81          | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 0.63/0.81  thf('214', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v2_struct_0 @ sk_A)
% 0.63/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                 sk_C @ (u1_struct_0 @ X0)))
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('simplify', [status(thm)], ['213'])).
% 0.63/0.81  thf('215', plain,
% 0.63/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.81        | (v2_struct_0 @ sk_B)
% 0.63/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.63/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81               sk_C @ (u1_struct_0 @ sk_A)))
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('sup-', [status(thm)], ['199', '214'])).
% 0.63/0.81  thf('216', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('217', plain,
% 0.63/0.81      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.63/0.81      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.63/0.81  thf('218', plain,
% 0.63/0.81      (((m1_subset_1 @ sk_C @ 
% 0.63/0.81         (k1_zfmisc_1 @ 
% 0.63/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.63/0.81         <= (((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('split', [status(esa)], ['173'])).
% 0.63/0.81  thf(d4_tmap_1, axiom,
% 0.63/0.81    (![A:$i]:
% 0.63/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.81       ( ![B:$i]:
% 0.63/0.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.63/0.81             ( l1_pre_topc @ B ) ) =>
% 0.63/0.81           ( ![C:$i]:
% 0.63/0.81             ( ( ( v1_funct_1 @ C ) & 
% 0.63/0.81                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.63/0.81                 ( m1_subset_1 @
% 0.63/0.81                   C @ 
% 0.63/0.81                   ( k1_zfmisc_1 @
% 0.63/0.81                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.63/0.81               ( ![D:$i]:
% 0.63/0.81                 ( ( m1_pre_topc @ D @ A ) =>
% 0.63/0.81                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.63/0.81                     ( k2_partfun1 @
% 0.63/0.81                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.63/0.81                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.63/0.81  thf('219', plain,
% 0.63/0.81      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.63/0.81         ((v2_struct_0 @ X7)
% 0.63/0.81          | ~ (v2_pre_topc @ X7)
% 0.63/0.81          | ~ (l1_pre_topc @ X7)
% 0.63/0.81          | ~ (m1_pre_topc @ X8 @ X9)
% 0.63/0.81          | ((k2_tmap_1 @ X9 @ X7 @ X10 @ X8)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10 @ 
% 0.63/0.81                 (u1_struct_0 @ X8)))
% 0.63/0.81          | ~ (m1_subset_1 @ X10 @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.63/0.81          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.63/0.81          | ~ (v1_funct_1 @ X10)
% 0.63/0.81          | ~ (l1_pre_topc @ X9)
% 0.63/0.81          | ~ (v2_pre_topc @ X9)
% 0.63/0.81          | (v2_struct_0 @ X9))),
% 0.63/0.81      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.63/0.81  thf('220', plain,
% 0.63/0.81      ((![X0 : $i]:
% 0.63/0.81          ((v2_struct_0 @ sk_A)
% 0.63/0.81           | ~ (v2_pre_topc @ sk_A)
% 0.63/0.81           | ~ (l1_pre_topc @ sk_A)
% 0.63/0.81           | ~ (v1_funct_1 @ sk_C)
% 0.63/0.81           | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81           | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.63/0.81               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                  sk_C @ (u1_struct_0 @ X0)))
% 0.63/0.81           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81           | ~ (l1_pre_topc @ sk_B)
% 0.63/0.81           | ~ (v2_pre_topc @ sk_B)
% 0.63/0.81           | (v2_struct_0 @ sk_B)))
% 0.63/0.81         <= (((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('sup-', [status(thm)], ['218', '219'])).
% 0.63/0.81  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('224', plain,
% 0.63/0.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('225', plain, ((l1_pre_topc @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('226', plain, ((v2_pre_topc @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('227', plain,
% 0.63/0.81      ((![X0 : $i]:
% 0.63/0.81          ((v2_struct_0 @ sk_A)
% 0.63/0.81           | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.63/0.81               = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                  sk_C @ (u1_struct_0 @ X0)))
% 0.63/0.81           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81           | (v2_struct_0 @ sk_B)))
% 0.63/0.81         <= (((m1_subset_1 @ sk_C @ 
% 0.63/0.81               (k1_zfmisc_1 @ 
% 0.63/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.63/0.81      inference('demod', [status(thm)],
% 0.63/0.81                ['220', '221', '222', '223', '224', '225', '226'])).
% 0.63/0.81  thf('228', plain,
% 0.63/0.81      (((m1_subset_1 @ sk_C @ 
% 0.63/0.81         (k1_zfmisc_1 @ 
% 0.63/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.63/0.81      inference('sat_resolution*', [status(thm)], ['182'])).
% 0.63/0.81  thf('229', plain,
% 0.63/0.81      (![X0 : $i]:
% 0.63/0.81         ((v2_struct_0 @ sk_A)
% 0.63/0.81          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.63/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81                 sk_C @ (u1_struct_0 @ X0)))
% 0.63/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.63/0.81          | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('simpl_trail', [status(thm)], ['227', '228'])).
% 0.63/0.81  thf('230', plain,
% 0.63/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.81        | (v2_struct_0 @ sk_B)
% 0.63/0.81        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.63/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81               sk_C @ (u1_struct_0 @ sk_A)))
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('sup-', [status(thm)], ['217', '229'])).
% 0.63/0.81  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('232', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.63/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81               sk_C @ (u1_struct_0 @ sk_A)))
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)], ['230', '231'])).
% 0.63/0.81  thf('233', plain, (~ (v2_struct_0 @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('234', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_A)
% 0.63/0.81        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.63/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.63/0.81               sk_C @ (u1_struct_0 @ sk_A))))),
% 0.63/0.81      inference('clc', [status(thm)], ['232', '233'])).
% 0.63/0.81  thf('235', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('236', plain,
% 0.63/0.81      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.63/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81            (u1_struct_0 @ sk_A)))),
% 0.63/0.81      inference('clc', [status(thm)], ['234', '235'])).
% 0.63/0.81  thf('237', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.63/0.81            = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)], ['215', '216', '236'])).
% 0.63/0.81  thf('238', plain, (~ (v2_struct_0 @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('239', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_A)
% 0.63/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.63/0.81            = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('clc', [status(thm)], ['237', '238'])).
% 0.63/0.81  thf('240', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('241', plain,
% 0.63/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.63/0.81         = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.63/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.63/0.81  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('243', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('244', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | (v2_struct_0 @ sk_A)
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)], ['197', '198', '241', '242', '243'])).
% 0.63/0.81  thf('245', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_A)
% 0.63/0.81        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('simplify', [status(thm)], ['244'])).
% 0.63/0.81  thf('246', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('247', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('clc', [status(thm)], ['245', '246'])).
% 0.63/0.81  thf('248', plain, (~ (v2_struct_0 @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('249', plain,
% 0.63/0.81      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.63/0.81        (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.63/0.81      inference('clc', [status(thm)], ['247', '248'])).
% 0.63/0.81  thf('250', plain,
% 0.63/0.81      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.63/0.81             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.63/0.81        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('demod', [status(thm)], ['187', '249'])).
% 0.63/0.81  thf('251', plain,
% 0.63/0.81      ((~ (l1_struct_0 @ sk_A)
% 0.63/0.81        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['171', '250'])).
% 0.63/0.81  thf('252', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.63/0.81  thf('253', plain,
% 0.63/0.81      ((((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.63/0.81        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('demod', [status(thm)], ['251', '252'])).
% 0.63/0.81  thf('254', plain,
% 0.63/0.81      ((~ (l1_struct_0 @ sk_A)
% 0.63/0.81        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.63/0.81      inference('sup-', [status(thm)], ['170', '253'])).
% 0.63/0.81  thf('255', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.63/0.81  thf('256', plain, (((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)], ['254', '255'])).
% 0.63/0.81  thf('257', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_B)
% 0.63/0.81        | (v2_struct_0 @ sk_E)
% 0.63/0.81        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.63/0.81        | (v2_struct_0 @ sk_D)
% 0.63/0.81        | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('demod', [status(thm)], ['169', '256'])).
% 0.63/0.81  thf('258', plain,
% 0.63/0.81      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.63/0.81         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.63/0.81      inference('split', [status(esa)], ['15'])).
% 0.63/0.81  thf('259', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.63/0.81      inference('sat_resolution*', [status(thm)], ['136', '147'])).
% 0.63/0.81  thf('260', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.63/0.81      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 0.63/0.81  thf('261', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_A)
% 0.63/0.81        | (v2_struct_0 @ sk_D)
% 0.63/0.81        | (v2_struct_0 @ sk_E)
% 0.63/0.81        | (v2_struct_0 @ sk_B))),
% 0.63/0.81      inference('sup-', [status(thm)], ['257', '260'])).
% 0.63/0.81  thf('262', plain, (~ (v2_struct_0 @ sk_B)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('263', plain,
% 0.63/0.81      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.63/0.81      inference('sup-', [status(thm)], ['261', '262'])).
% 0.63/0.81  thf('264', plain, (~ (v2_struct_0 @ sk_E)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('265', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.63/0.81      inference('clc', [status(thm)], ['263', '264'])).
% 0.63/0.81  thf('266', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.81  thf('267', plain, ((v2_struct_0 @ sk_D)),
% 0.63/0.81      inference('clc', [status(thm)], ['265', '266'])).
% 0.63/0.81  thf('268', plain, ($false), inference('demod', [status(thm)], ['0', '267'])).
% 0.63/0.81  
% 0.63/0.81  % SZS output end Refutation
% 0.63/0.81  
% 0.63/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
