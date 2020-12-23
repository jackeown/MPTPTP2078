%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.71W2eceKjo

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 340 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   22
%              Number of atoms          : 1638 (13130 expanded)
%              Number of equality atoms :   14 ( 171 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t66_tmap_1,conjecture,(
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
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ( ( ( v3_pre_topc @ E @ B )
                                    & ( r2_hidden @ F @ E )
                                    & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                    & ( F = G ) )
                                 => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                  <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r1_tmap_1 @ X16 @ X18 @ ( k2_tmap_1 @ X15 @ X18 @ X19 @ X16 ) @ X17 )
      | ( X20 != X17 )
      | ~ ( r1_tmap_1 @ X15 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X18 @ X19 @ X17 )
      | ( r1_tmap_1 @ X16 @ X18 @ ( k2_tmap_1 @ X15 @ X18 @ X19 @ X16 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('42',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['7','40','41'])).

thf('43',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['3','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
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
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X24 @ X21 @ X23 )
      | ( X23 != X25 )
      | ~ ( r1_tmap_1 @ X22 @ X26 @ ( k2_tmap_1 @ X21 @ X26 @ X27 @ X22 ) @ X25 )
      | ( r1_tmap_1 @ X21 @ X26 @ X27 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('46',plain,(
    ! [X21: $i,X22: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( r1_tmap_1 @ X21 @ X26 @ X27 @ X25 )
      | ~ ( r1_tmap_1 @ X22 @ X26 @ ( k2_tmap_1 @ X21 @ X26 @ X27 @ X22 ) @ X25 )
      | ~ ( m1_connsp_2 @ X24 @ X21 @ X25 )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('58',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','59'])).

thf('61',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k1_tops_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_E )
    | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['72','74'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('76',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ sk_G @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['64','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ( m1_connsp_2 @ X14 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('89',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','91'])).

thf('93',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['32'])).

thf('94',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['2'])).

thf('97',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('100',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['7','40','100'])).

thf('102',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['95','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.71W2eceKjo
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 99 iterations in 0.035s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(t66_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @
% 0.21/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                           ( ![G:$i]:
% 0.21/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.53                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.53                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.53                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.53                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.53                                   ( r1_tmap_1 @
% 0.21/0.53                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53                ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                    ( v1_funct_2 @
% 0.21/0.53                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                    ( m1_subset_1 @
% 0.21/0.53                      C @ 
% 0.21/0.53                      ( k1_zfmisc_1 @
% 0.21/0.53                        ( k2_zfmisc_1 @
% 0.21/0.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @
% 0.21/0.53                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                          ( ![F:$i]:
% 0.21/0.53                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                              ( ![G:$i]:
% 0.21/0.53                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.53                                      ( r2_hidden @ F @ E ) & 
% 0.21/0.53                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.53                                      ( ( F ) = ( G ) ) ) =>
% 0.21/0.53                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.53                                      ( r1_tmap_1 @
% 0.21/0.53                                        D @ A @ 
% 0.21/0.53                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53           sk_G)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53           sk_G)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)) | 
% 0.21/0.53       ~
% 0.21/0.53       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G))),
% 0.21/0.53      inference('split', [status(esa)], ['6'])).
% 0.21/0.53  thf('8', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t64_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.53                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.53                             ( r1_tmap_1 @
% 0.21/0.53                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X15)
% 0.21/0.53          | ~ (v2_pre_topc @ X15)
% 0.21/0.53          | ~ (l1_pre_topc @ X15)
% 0.21/0.53          | (v2_struct_0 @ X16)
% 0.21/0.53          | ~ (m1_pre_topc @ X16 @ X15)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.53          | (r1_tmap_1 @ X16 @ X18 @ (k2_tmap_1 @ X15 @ X18 @ X19 @ X16) @ X17)
% 0.21/0.53          | ((X20) != (X17))
% 0.21/0.53          | ~ (r1_tmap_1 @ X15 @ X18 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X18))))
% 0.21/0.53          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X18))
% 0.21/0.53          | ~ (v1_funct_1 @ X19)
% 0.21/0.53          | ~ (l1_pre_topc @ X18)
% 0.21/0.53          | ~ (v2_pre_topc @ X18)
% 0.21/0.53          | (v2_struct_0 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X18)
% 0.21/0.53          | ~ (v2_pre_topc @ X18)
% 0.21/0.53          | ~ (l1_pre_topc @ X18)
% 0.21/0.53          | ~ (v1_funct_1 @ X19)
% 0.21/0.53          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X18))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X18))))
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.21/0.53          | ~ (r1_tmap_1 @ X15 @ X18 @ X19 @ X17)
% 0.21/0.53          | (r1_tmap_1 @ X16 @ X18 @ (k2_tmap_1 @ X15 @ X18 @ X19 @ X16) @ X17)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.53          | ~ (m1_pre_topc @ X16 @ X15)
% 0.21/0.53          | (v2_struct_0 @ X16)
% 0.21/0.53          | ~ (l1_pre_topc @ X15)
% 0.21/0.53          | ~ (v2_pre_topc @ X15)
% 0.21/0.53          | (v2_struct_0 @ X15))),
% 0.21/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.53  thf('17', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['16', '17', '18', '19', '20', '21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_A)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53              sk_G)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.21/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '23'])).
% 0.21/0.53  thf('25', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_A)
% 0.21/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53              sk_G)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.21/0.53           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_D)
% 0.21/0.53         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.53         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '28'])).
% 0.21/0.53  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_D)
% 0.21/0.53         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53           sk_G)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53           sk_G))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.53  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_D))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.21/0.53               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G)) | 
% 0.21/0.53       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G)) | 
% 0.21/0.53       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.53      inference('split', [status(esa)], ['11'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53         sk_G))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '40', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.21/0.53        sk_G)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['3', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t65_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @
% 0.21/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                           ( ![G:$i]:
% 0.21/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.53                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.21/0.53                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.53                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.53                                   ( r1_tmap_1 @
% 0.21/0.53                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X21)
% 0.21/0.53          | ~ (v2_pre_topc @ X21)
% 0.21/0.53          | ~ (l1_pre_topc @ X21)
% 0.21/0.53          | (v2_struct_0 @ X22)
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X21)
% 0.21/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (m1_connsp_2 @ X24 @ X21 @ X23)
% 0.21/0.53          | ((X23) != (X25))
% 0.21/0.53          | ~ (r1_tmap_1 @ X22 @ X26 @ (k2_tmap_1 @ X21 @ X26 @ X27 @ X22) @ 
% 0.21/0.53               X25)
% 0.21/0.53          | (r1_tmap_1 @ X21 @ X26 @ X27 @ X23)
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X26))))
% 0.21/0.53          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X26))
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ~ (l1_pre_topc @ X26)
% 0.21/0.53          | ~ (v2_pre_topc @ X26)
% 0.21/0.53          | (v2_struct_0 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X26)
% 0.21/0.53          | ~ (v2_pre_topc @ X26)
% 0.21/0.53          | ~ (l1_pre_topc @ X26)
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X26))
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X26))))
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.21/0.53          | (r1_tmap_1 @ X21 @ X26 @ X27 @ X25)
% 0.21/0.53          | ~ (r1_tmap_1 @ X22 @ X26 @ (k2_tmap_1 @ X21 @ X26 @ X27 @ X22) @ 
% 0.21/0.53               X25)
% 0.21/0.53          | ~ (m1_connsp_2 @ X24 @ X21 @ X25)
% 0.21/0.53          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X21)
% 0.21/0.53          | (v2_struct_0 @ X22)
% 0.21/0.53          | ~ (l1_pre_topc @ X21)
% 0.21/0.53          | ~ (v2_pre_topc @ X21)
% 0.21/0.53          | (v2_struct_0 @ X21))),
% 0.21/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53               X1)
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.53  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.53          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.21/0.53               X1)
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['47', '48', '49', '50', '51', '52', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '54'])).
% 0.21/0.53  thf('56', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('58', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))
% 0.21/0.53        | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '59'])).
% 0.21/0.53  thf('61', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('63', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.21/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t56_tops_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.53          | ~ (v3_pre_topc @ X9 @ X10)
% 0.21/0.53          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.53          | (r1_tarski @ X9 @ (k1_tops_1 @ X10 @ X11))
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.53          | ~ (l1_pre_topc @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.21/0.53          | ~ (r1_tarski @ sk_E @ X0)
% 0.21/0.53          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.53          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.21/0.53          | ~ (r1_tarski @ sk_E @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_E @ sk_E)
% 0.21/0.53        | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '71'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.53  thf('75', plain, ((r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.21/0.53      inference('demod', [status(thm)], ['72', '74'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (![X6 : $i, X8 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_B @ sk_E)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.53  thf(l3_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.53          | (r2_hidden @ X3 @ X5)
% 0.21/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.53  thf('80', plain, ((r2_hidden @ sk_G @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.21/0.53      inference('sup-', [status(thm)], ['64', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.53                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.53          | ~ (r2_hidden @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.21/0.53          | (m1_connsp_2 @ X14 @ X13 @ X12)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.53          | ~ (l1_pre_topc @ X13)
% 0.21/0.53          | ~ (v2_pre_topc @ X13)
% 0.21/0.53          | (v2_struct_0 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.53  thf('84', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.21/0.53        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['80', '86'])).
% 0.21/0.53  thf('88', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      (((m1_connsp_2 @ sk_E @ sk_B @ sk_G) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.53  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('91', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.21/0.53      inference('clc', [status(thm)], ['89', '90'])).
% 0.21/0.53  thf('92', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['60', '61', '91'])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('94', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('97', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.53  thf('99', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['6'])).
% 0.21/0.53  thf('100', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)) | 
% 0.21/0.53       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.21/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.53  thf('101', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '40', '100'])).
% 0.21/0.53  thf('102', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['95', '101'])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['92', '102'])).
% 0.21/0.53  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('105', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.21/0.53      inference('clc', [status(thm)], ['103', '104'])).
% 0.21/0.53  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('107', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('clc', [status(thm)], ['105', '106'])).
% 0.21/0.53  thf('108', plain, ($false), inference('demod', [status(thm)], ['0', '107'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
