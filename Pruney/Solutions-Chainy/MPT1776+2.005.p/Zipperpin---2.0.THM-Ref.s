%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fbda8ZUGZJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 705 expanded)
%              Number of leaves         :   36 ( 216 expanded)
%              Depth                    :   29
%              Number of atoms          : 2073 (27322 expanded)
%              Number of equality atoms :   27 ( 379 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( ( k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X22 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( k2_tmap_1 @ X16 @ X14 @ X17 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X17 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('29',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','32','37','38','39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['4'])).

thf('55',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( v1_tsep_1 @ X35 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ ( k2_tmap_1 @ X34 @ X37 @ X38 @ X35 ) @ X36 )
      | ( r1_tmap_1 @ X34 @ X37 @ X38 @ X39 )
      | ( X39 != X36 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ( r1_tmap_1 @ X34 @ X37 @ X38 @ X36 )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ ( k2_tmap_1 @ X34 @ X37 @ X38 @ X35 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_tsep_1 @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('63',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('64',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('72',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('80',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

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

thf('86',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X25 ) )
      | ( v1_tsep_1 @ X23 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','87'])).

thf('89',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['69','70','71','72','97'])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['4'])).

thf('108',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['7','106','107'])).

thf('109',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['5','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ( X33 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('112',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X30 )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('115',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('116',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['109','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('128',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('131',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['7','106'])).

thf('133',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fbda8ZUGZJ
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:24:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 118 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(t87_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.20/0.50                           ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.50                         ( ![F:$i]:
% 0.20/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                             ( ![G:$i]:
% 0.20/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.50                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.50                                     ( r1_tmap_1 @
% 0.20/0.50                                       C @ A @ 
% 0.20/0.50                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50                ( l1_pre_topc @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                      ( ![E:$i]:
% 0.20/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                            ( v1_funct_2 @
% 0.20/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                            ( m1_subset_1 @
% 0.20/0.50                              E @ 
% 0.20/0.50                              ( k1_zfmisc_1 @
% 0.20/0.50                                ( k2_zfmisc_1 @
% 0.20/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.20/0.50                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.50                            ( ![F:$i]:
% 0.20/0.50                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                                ( ![G:$i]:
% 0.20/0.50                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.50                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.50                                        ( r1_tmap_1 @
% 0.20/0.50                                          C @ A @ 
% 0.20/0.50                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.20/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.20/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.20/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('8', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d5_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.50                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.50                           ( k2_partfun1 @
% 0.20/0.50                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.50                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X18)
% 0.20/0.50          | ~ (v2_pre_topc @ X18)
% 0.20/0.50          | ~ (l1_pre_topc @ X18)
% 0.20/0.50          | ~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.50          | ~ (m1_pre_topc @ X19 @ X21)
% 0.20/0.50          | ((k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.20/0.50                 X22 @ (u1_struct_0 @ X19)))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))))
% 0.20/0.50          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))
% 0.20/0.50          | ~ (v1_funct_1 @ X22)
% 0.20/0.50          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.50          | ~ (l1_pre_topc @ X20)
% 0.20/0.50          | ~ (v2_pre_topc @ X20)
% 0.20/0.50          | (v2_struct_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.50  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.20/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.50        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '21'])).
% 0.20/0.50  thf('23', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d4_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.50                     ( k2_partfun1 @
% 0.20/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X14)
% 0.20/0.50          | ~ (v2_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.50          | ((k2_tmap_1 @ X16 @ X14 @ X17 @ X15)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14) @ 
% 0.20/0.50                 X17 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))))
% 0.20/0.50          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))
% 0.20/0.50          | ~ (v1_funct_1 @ X17)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X7 @ X8)
% 0.20/0.50          | (v2_pre_topc @ X7)
% 0.20/0.50          | ~ (l1_pre_topc @ X8)
% 0.20/0.50          | ~ (v2_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.50  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.50          | (l1_pre_topc @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('35', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['26', '32', '37', '38', '39', '40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.20/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.50        | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '42'])).
% 0.20/0.50  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_D)
% 0.20/0.50        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.20/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.20/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.20/0.50            (u1_struct_0 @ sk_C_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.20/0.50            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '47', '48'])).
% 0.20/0.50  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.20/0.50            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.20/0.50         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('55', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['53', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t67_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.20/0.50                     ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                           ( ( ( E ) = ( F ) ) =>
% 0.20/0.50                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.20/0.50                               ( r1_tmap_1 @
% 0.20/0.50                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X34)
% 0.20/0.50          | ~ (v2_pre_topc @ X34)
% 0.20/0.50          | ~ (l1_pre_topc @ X34)
% 0.20/0.50          | (v2_struct_0 @ X35)
% 0.20/0.50          | ~ (v1_tsep_1 @ X35 @ X34)
% 0.20/0.50          | ~ (m1_pre_topc @ X35 @ X34)
% 0.20/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 0.20/0.50          | ~ (r1_tmap_1 @ X35 @ X37 @ (k2_tmap_1 @ X34 @ X37 @ X38 @ X35) @ 
% 0.20/0.50               X36)
% 0.20/0.50          | (r1_tmap_1 @ X34 @ X37 @ X38 @ X39)
% 0.20/0.50          | ((X39) != (X36))
% 0.20/0.50          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X34))
% 0.20/0.50          | ~ (m1_subset_1 @ X38 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))))
% 0.20/0.50          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))
% 0.20/0.50          | ~ (v1_funct_1 @ X38)
% 0.20/0.50          | ~ (l1_pre_topc @ X37)
% 0.20/0.50          | ~ (v2_pre_topc @ X37)
% 0.20/0.50          | (v2_struct_0 @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X37)
% 0.20/0.50          | ~ (v2_pre_topc @ X37)
% 0.20/0.50          | ~ (l1_pre_topc @ X37)
% 0.20/0.50          | ~ (v1_funct_1 @ X38)
% 0.20/0.50          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))
% 0.20/0.50          | ~ (m1_subset_1 @ X38 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))))
% 0.20/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.20/0.50          | (r1_tmap_1 @ X34 @ X37 @ X38 @ X36)
% 0.20/0.50          | ~ (r1_tmap_1 @ X35 @ X37 @ (k2_tmap_1 @ X34 @ X37 @ X38 @ X35) @ 
% 0.20/0.50               X36)
% 0.20/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 0.20/0.50          | ~ (m1_pre_topc @ X35 @ X34)
% 0.20/0.50          | ~ (v1_tsep_1 @ X35 @ X34)
% 0.20/0.50          | (v2_struct_0 @ X35)
% 0.20/0.50          | ~ (l1_pre_topc @ X34)
% 0.20/0.50          | ~ (v2_pre_topc @ X34)
% 0.20/0.50          | (v2_struct_0 @ X34))),
% 0.20/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.50               X1)
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '60'])).
% 0.20/0.50  thf('62', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.50  thf('63', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.50               X1)
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['61', '62', '63', '64', '65', '66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.50         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.50         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.50         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.50         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.20/0.50         | (v2_struct_0 @ sk_C_1)
% 0.20/0.50         | (v2_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '68'])).
% 0.20/0.50  thf('70', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('71', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('72', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('75', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t1_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( m1_subset_1 @
% 0.20/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.50          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.50          | ~ (l1_pre_topc @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.50  thf(l3_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.50          | (r2_hidden @ X4 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.20/0.50             (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '81'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.50  thf(t19_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.50         (~ (v1_tsep_1 @ X23 @ X24)
% 0.20/0.50          | ~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.50          | ~ (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X25))
% 0.20/0.50          | (v1_tsep_1 @ X23 @ X25)
% 0.20/0.50          | ~ (m1_pre_topc @ X25 @ X24)
% 0.20/0.50          | (v2_struct_0 @ X25)
% 0.20/0.50          | ~ (l1_pre_topc @ X24)
% 0.20/0.50          | ~ (v2_pre_topc @ X24)
% 0.20/0.50          | (v2_struct_0 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.50          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((~ (v1_tsep_1 @ sk_C_1 @ sk_B)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.20/0.50        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '87'])).
% 0.20/0.50  thf('89', plain, ((v1_tsep_1 @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('90', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('92', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.20/0.50  thf('94', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('95', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('clc', [status(thm)], ['93', '94'])).
% 0.20/0.50  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.50         | (v2_struct_0 @ sk_C_1)
% 0.20/0.50         | (v2_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['69', '70', '71', '72', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.50  thf('101', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.50  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C_1))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('clc', [status(thm)], ['102', '103'])).
% 0.20/0.50  thf('105', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('106', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.50       ~
% 0.20/0.50       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.50      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.50  thf('107', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.50       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('108', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['7', '106', '107'])).
% 0.20/0.50  thf('109', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['5', '108'])).
% 0.20/0.50  thf('110', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t64_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                           ( ( ( ( E ) = ( F ) ) & 
% 0.20/0.50                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.20/0.50                             ( r1_tmap_1 @
% 0.20/0.50                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X28)
% 0.20/0.50          | ~ (v2_pre_topc @ X28)
% 0.20/0.50          | ~ (l1_pre_topc @ X28)
% 0.20/0.50          | (v2_struct_0 @ X29)
% 0.20/0.50          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.50          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.50          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.20/0.50          | ((X33) != (X30))
% 0.20/0.50          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X33)
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.20/0.50          | ~ (m1_subset_1 @ X32 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.20/0.50          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.20/0.50          | ~ (v1_funct_1 @ X32)
% 0.20/0.50          | ~ (l1_pre_topc @ X31)
% 0.20/0.50          | ~ (v2_pre_topc @ X31)
% 0.20/0.50          | (v2_struct_0 @ X31))),
% 0.20/0.50      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.20/0.50  thf('112', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X31)
% 0.20/0.50          | ~ (v2_pre_topc @ X31)
% 0.20/0.50          | ~ (l1_pre_topc @ X31)
% 0.20/0.50          | ~ (v1_funct_1 @ X32)
% 0.20/0.50          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.20/0.50          | ~ (m1_subset_1 @ X32 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.20/0.50          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.50          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X30)
% 0.20/0.50          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.20/0.50          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.50          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.50          | (v2_struct_0 @ X29)
% 0.20/0.50          | ~ (l1_pre_topc @ X28)
% 0.20/0.50          | ~ (v2_pre_topc @ X28)
% 0.20/0.50          | (v2_struct_0 @ X28))),
% 0.20/0.50      inference('simplify', [status(thm)], ['111'])).
% 0.20/0.50  thf('113', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['110', '112'])).
% 0.20/0.50  thf('114', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.50  thf('115', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('116', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('117', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('120', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['113', '114', '115', '116', '117', '118', '119'])).
% 0.20/0.50  thf('121', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.50             sk_F)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['109', '120'])).
% 0.20/0.50  thf('122', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('123', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.50             sk_F)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['121', '122'])).
% 0.20/0.50  thf('124', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_C_1)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.50        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '123'])).
% 0.20/0.50  thf('125', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('126', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_C_1)
% 0.20/0.50        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['124', '125'])).
% 0.20/0.50  thf('127', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('128', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('129', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['127', '128'])).
% 0.20/0.50  thf('130', plain,
% 0.20/0.50      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.20/0.50         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('131', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['129', '130'])).
% 0.20/0.50  thf('132', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['7', '106'])).
% 0.20/0.50  thf('133', plain,
% 0.20/0.50      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.50          (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['131', '132'])).
% 0.20/0.50  thf('134', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['126', '133'])).
% 0.20/0.50  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('136', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['134', '135'])).
% 0.20/0.50  thf('137', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('138', plain, ((v2_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('clc', [status(thm)], ['136', '137'])).
% 0.20/0.50  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
