%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xGhcrCr1OR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 422 expanded)
%              Number of leaves         :   27 ( 128 expanded)
%              Depth                    :   29
%              Number of atoms          : 1788 (17107 expanded)
%              Number of equality atoms :   11 ( 217 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t87_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ( ( v1_tsep_1 @ C @ B )
                            & ( m1_pre_topc @ C @ B )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_tmap_1,axiom,(
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
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_tsep_1 @ X17 @ X15 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( X18 != X19 )
      | ~ ( r1_tmap_1 @ X17 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20 ) @ X19 )
      | ( r1_tmap_1 @ X15 @ X14 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tmap_1 @ X15 @ X14 @ X20 @ X19 )
      | ~ ( r1_tmap_1 @ X17 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( v1_tsep_1 @ X17 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r1_tarski @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_tsep_1 @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X4 ) )
      | ( v1_tsep_1 @ X2 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','60','61'])).

thf('63',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('74',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['15','19','72','73'])).

thf('75',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['6','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_pre_topc @ X8 @ X11 )
      | ~ ( r1_tmap_1 @ X11 @ X7 @ X12 @ X10 )
      | ( X10 != X13 )
      | ( r1_tmap_1 @ X8 @ X7 @ ( k3_tmap_1 @ X9 @ X7 @ X11 @ X8 @ X12 ) @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X9 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X9 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X8 ) )
      | ( r1_tmap_1 @ X8 @ X7 @ ( k3_tmap_1 @ X9 @ X7 @ X11 @ X8 @ X12 ) @ X13 )
      | ~ ( r1_tmap_1 @ X11 @ X7 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('97',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['15','19','72','99'])).

thf('101',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['96','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xGhcrCr1OR
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 57 iterations in 0.034s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(t87_tmap_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                         ( v1_funct_2 @
% 0.21/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50                         ( m1_subset_1 @
% 0.21/0.50                           E @ 
% 0.21/0.50                           ( k1_zfmisc_1 @
% 0.21/0.50                             ( k2_zfmisc_1 @
% 0.21/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.50                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.21/0.50                           ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.50                         ( ![F:$i]:
% 0.21/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                             ( ![G:$i]:
% 0.21/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.21/0.50                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.21/0.50                                     ( r1_tmap_1 @
% 0.21/0.50                                       C @ A @ 
% 0.21/0.50                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50                ( l1_pre_topc @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.50                      ( ![E:$i]:
% 0.21/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                            ( v1_funct_2 @
% 0.21/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50                            ( m1_subset_1 @
% 0.21/0.50                              E @ 
% 0.21/0.50                              ( k1_zfmisc_1 @
% 0.21/0.50                                ( k2_zfmisc_1 @
% 0.21/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.50                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.21/0.50                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.50                            ( ![F:$i]:
% 0.21/0.50                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                                ( ![G:$i]:
% 0.21/0.50                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                                    ( ( ( F ) = ( G ) ) =>
% 0.21/0.50                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.21/0.50                                        ( r1_tmap_1 @
% 0.21/0.50                                          C @ A @ 
% 0.21/0.50                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain, (((sk_F) = (sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, (((sk_F) = (sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('split', [status(esa)], ['11'])).
% 0.21/0.50  thf('13', plain, (((sk_F) = (sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain, (((sk_F) = (sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.21/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('split', [status(esa)], ['18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('21', plain, (((sk_F) = (sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t86_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                         ( v1_funct_2 @
% 0.21/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                         ( m1_subset_1 @
% 0.21/0.50                           E @ 
% 0.21/0.50                           ( k1_zfmisc_1 @
% 0.21/0.50                             ( k2_zfmisc_1 @
% 0.21/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.50                         ( ![F:$i]:
% 0.21/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                             ( ![G:$i]:
% 0.21/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.21/0.50                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.21/0.50                                     ( r1_tmap_1 @
% 0.21/0.50                                       C @ B @ 
% 0.21/0.50                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X14)
% 0.21/0.50          | ~ (v2_pre_topc @ X14)
% 0.21/0.50          | ~ (l1_pre_topc @ X14)
% 0.21/0.50          | (v2_struct_0 @ X15)
% 0.21/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.50          | ~ (v1_tsep_1 @ X17 @ X15)
% 0.21/0.50          | ~ (m1_pre_topc @ X17 @ X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.21/0.50          | ((X18) != (X19))
% 0.21/0.50          | ~ (r1_tmap_1 @ X17 @ X14 @ 
% 0.21/0.50               (k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20) @ X19)
% 0.21/0.50          | (r1_tmap_1 @ X15 @ X14 @ X20 @ X18)
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.21/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (v1_funct_1 @ X20)
% 0.21/0.50          | ~ (m1_pre_topc @ X17 @ X16)
% 0.21/0.50          | (v2_struct_0 @ X17)
% 0.21/0.50          | ~ (l1_pre_topc @ X16)
% 0.21/0.50          | ~ (v2_pre_topc @ X16)
% 0.21/0.50          | (v2_struct_0 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X16)
% 0.21/0.50          | ~ (v2_pre_topc @ X16)
% 0.21/0.50          | ~ (l1_pre_topc @ X16)
% 0.21/0.50          | (v2_struct_0 @ X17)
% 0.21/0.50          | ~ (m1_pre_topc @ X17 @ X16)
% 0.21/0.50          | ~ (v1_funct_1 @ X20)
% 0.21/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.50          | (r1_tmap_1 @ X15 @ X14 @ X20 @ X19)
% 0.21/0.50          | ~ (r1_tmap_1 @ X17 @ X14 @ 
% 0.21/0.50               (k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20) @ X19)
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.21/0.50          | ~ (m1_pre_topc @ X17 @ X15)
% 0.21/0.50          | ~ (v1_tsep_1 @ X17 @ X15)
% 0.21/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.50          | (v2_struct_0 @ X15)
% 0.21/0.50          | ~ (l1_pre_topc @ X14)
% 0.21/0.50          | ~ (v2_pre_topc @ X14)
% 0.21/0.50          | (v2_struct_0 @ X14))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.21/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.50  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.21/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B)
% 0.21/0.50         | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.21/0.50         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.50         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.21/0.50         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.21/0.50         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.50         | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.50         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.50         | (v2_struct_0 @ sk_D)
% 0.21/0.50         | (v2_struct_0 @ sk_A)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '31'])).
% 0.21/0.50  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('37', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t35_borsuk_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.50          | (r1_tarski @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.50        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('45', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '47'])).
% 0.21/0.50  thf(t19_tsep_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (v1_tsep_1 @ X2 @ X3)
% 0.21/0.50          | ~ (m1_pre_topc @ X2 @ X3)
% 0.21/0.50          | ~ (r1_tarski @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X4))
% 0.21/0.50          | (v1_tsep_1 @ X2 @ X4)
% 0.21/0.50          | ~ (m1_pre_topc @ X4 @ X3)
% 0.21/0.50          | (v2_struct_0 @ X4)
% 0.21/0.50          | ~ (l1_pre_topc @ X3)
% 0.21/0.50          | ~ (v2_pre_topc @ X3)
% 0.21/0.50          | (v2_struct_0 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.21/0.50        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.21/0.50        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '50'])).
% 0.21/0.50  thf('52', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.21/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.21/0.50      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf('61', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.21/0.50         | (v2_struct_0 @ sk_D)
% 0.21/0.50         | (v2_struct_0 @ sk_A)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['32', '33', '34', '35', '36', '37', '38', '60', '61'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['11'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A)
% 0.21/0.50         | (v2_struct_0 @ sk_D)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | (v2_struct_0 @ sk_B)))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.50  thf('69', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_C))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.21/0.50       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.50      inference('split', [status(esa)], ['9'])).
% 0.21/0.50  thf('74', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['15', '19', '72', '73'])).
% 0.21/0.50  thf('75', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['6', '74'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t81_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                         ( v1_funct_2 @
% 0.21/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                         ( m1_subset_1 @
% 0.21/0.50                           E @ 
% 0.21/0.50                           ( k1_zfmisc_1 @
% 0.21/0.50                             ( k2_zfmisc_1 @
% 0.21/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50                       ( ![F:$i]:
% 0.21/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                           ( ![G:$i]:
% 0.21/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                               ( ( ( ( F ) = ( G ) ) & 
% 0.21/0.50                                   ( m1_pre_topc @ D @ C ) & 
% 0.21/0.50                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.21/0.50                                 ( r1_tmap_1 @
% 0.21/0.50                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X7)
% 0.21/0.50          | ~ (v2_pre_topc @ X7)
% 0.21/0.50          | ~ (l1_pre_topc @ X7)
% 0.21/0.50          | (v2_struct_0 @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.21/0.50          | ~ (m1_pre_topc @ X8 @ X11)
% 0.21/0.50          | ~ (r1_tmap_1 @ X11 @ X7 @ X12 @ X10)
% 0.21/0.50          | ((X10) != (X13))
% 0.21/0.50          | (r1_tmap_1 @ X8 @ X7 @ (k3_tmap_1 @ X9 @ X7 @ X11 @ X8 @ X12) @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X8))
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X7))))
% 0.21/0.50          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X7))
% 0.21/0.50          | ~ (v1_funct_1 @ X12)
% 0.21/0.50          | ~ (m1_pre_topc @ X11 @ X9)
% 0.21/0.50          | (v2_struct_0 @ X11)
% 0.21/0.50          | ~ (l1_pre_topc @ X9)
% 0.21/0.50          | ~ (v2_pre_topc @ X9)
% 0.21/0.50          | (v2_struct_0 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X9)
% 0.21/0.50          | ~ (v2_pre_topc @ X9)
% 0.21/0.50          | ~ (l1_pre_topc @ X9)
% 0.21/0.50          | (v2_struct_0 @ X11)
% 0.21/0.50          | ~ (m1_pre_topc @ X11 @ X9)
% 0.21/0.50          | ~ (v1_funct_1 @ X12)
% 0.21/0.50          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X7))
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X7))))
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X8))
% 0.21/0.50          | (r1_tmap_1 @ X8 @ X7 @ (k3_tmap_1 @ X9 @ X7 @ X11 @ X8 @ X12) @ X13)
% 0.21/0.50          | ~ (r1_tmap_1 @ X11 @ X7 @ X12 @ X13)
% 0.21/0.50          | ~ (m1_pre_topc @ X8 @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.50          | ~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.50          | (v2_struct_0 @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X7)
% 0.21/0.50          | ~ (v2_pre_topc @ X7)
% 0.21/0.50          | (v2_struct_0 @ X7))),
% 0.21/0.50      inference('simplify', [status(thm)], ['77'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.21/0.50          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.50             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ X1)
% 0.21/0.50          | ~ (v2_pre_topc @ X1)
% 0.21/0.50          | (v2_struct_0 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['76', '78'])).
% 0.21/0.50  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.21/0.50          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.50             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ X1)
% 0.21/0.50          | ~ (v2_pre_topc @ X1)
% 0.21/0.50          | (v2_struct_0 @ X1))),
% 0.21/0.50      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.50          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.50             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '84'])).
% 0.21/0.50  thf('86', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.50          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.50             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_C)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.50          | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '87'])).
% 0.21/0.50  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_C)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.50        | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '90'])).
% 0.21/0.50  thf('92', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('94', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('97', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['18'])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.50      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['15', '19', '72', '99'])).
% 0.21/0.50  thf('101', plain,
% 0.21/0.50      (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.50          (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['96', '100'])).
% 0.21/0.50  thf('102', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['95', '101'])).
% 0.21/0.50  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.50  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('106', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('clc', [status(thm)], ['104', '105'])).
% 0.21/0.50  thf('107', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('108', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('clc', [status(thm)], ['106', '107'])).
% 0.21/0.50  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
