%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hs7cEg9mEg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:50 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 371 expanded)
%              Number of leaves         :   31 ( 114 expanded)
%              Depth                    :   22
%              Number of atoms          : 1646 (14444 expanded)
%              Number of equality atoms :   14 ( 191 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r1_tmap_1 @ X14 @ X16 @ ( k2_tmap_1 @ X13 @ X16 @ X17 @ X14 ) @ X15 )
      | ( X18 != X15 )
      | ~ ( r1_tmap_1 @ X13 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_tmap_1 @ X13 @ X16 @ X17 @ X15 )
      | ( r1_tmap_1 @ X14 @ X16 @ ( k2_tmap_1 @ X13 @ X16 @ X17 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['17','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['12'])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('49',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['7','16','47','48'])).

thf('50',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['3','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X21 )
      | ( X21 != X23 )
      | ~ ( r1_tmap_1 @ X20 @ X24 @ ( k2_tmap_1 @ X19 @ X24 @ X25 @ X20 ) @ X23 )
      | ( r1_tmap_1 @ X19 @ X24 @ X25 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X19 @ X24 @ X25 @ X23 )
      | ~ ( r1_tmap_1 @ X20 @ X24 @ ( k2_tmap_1 @ X19 @ X24 @ X25 @ X20 ) @ X23 )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X23 )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('65',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','66'])).

thf('68',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k1_tops_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_E )
    | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['79','81'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r2_hidden @ sk_G @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ( m1_connsp_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('94',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','96'])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('99',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('100',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('101',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['7','16','47','101'])).

thf('103',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['98','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hs7cEg9mEg
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.54  % Solved by: fo/fo7.sh
% 0.33/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.54  % done 69 iterations in 0.060s
% 0.33/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.54  % SZS output start Refutation
% 0.33/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.33/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.33/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.33/0.54  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.33/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.33/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.33/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.33/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.33/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.33/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.33/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.33/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.33/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.33/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.33/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.33/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.33/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.33/0.54  thf(t66_tmap_1, conjecture,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54             ( l1_pre_topc @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.33/0.54                 ( m1_subset_1 @
% 0.33/0.54                   C @ 
% 0.33/0.54                   ( k1_zfmisc_1 @
% 0.33/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.33/0.54               ( ![D:$i]:
% 0.33/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.33/0.54                   ( ![E:$i]:
% 0.33/0.54                     ( ( m1_subset_1 @
% 0.33/0.54                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.33/0.54                       ( ![F:$i]:
% 0.33/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.33/0.54                           ( ![G:$i]:
% 0.33/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.33/0.54                                   ( r2_hidden @ F @ E ) & 
% 0.33/0.54                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.33/0.54                                   ( ( F ) = ( G ) ) ) =>
% 0.33/0.54                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.33/0.54                                   ( r1_tmap_1 @
% 0.33/0.54                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.54    (~( ![A:$i]:
% 0.33/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.33/0.54            ( l1_pre_topc @ A ) ) =>
% 0.33/0.54          ( ![B:$i]:
% 0.33/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54                ( l1_pre_topc @ B ) ) =>
% 0.33/0.54              ( ![C:$i]:
% 0.33/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                    ( v1_funct_2 @
% 0.33/0.54                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.33/0.54                    ( m1_subset_1 @
% 0.33/0.54                      C @ 
% 0.33/0.54                      ( k1_zfmisc_1 @
% 0.33/0.54                        ( k2_zfmisc_1 @
% 0.33/0.54                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.33/0.54                  ( ![D:$i]:
% 0.33/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.33/0.54                      ( ![E:$i]:
% 0.33/0.54                        ( ( m1_subset_1 @
% 0.33/0.54                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.33/0.54                          ( ![F:$i]:
% 0.33/0.54                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.33/0.54                              ( ![G:$i]:
% 0.33/0.54                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.33/0.54                                      ( r2_hidden @ F @ E ) & 
% 0.33/0.54                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.33/0.54                                      ( ( F ) = ( G ) ) ) =>
% 0.33/0.54                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.33/0.54                                      ( r1_tmap_1 @
% 0.33/0.54                                        D @ A @ 
% 0.33/0.54                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.33/0.54    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.33/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('1', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('2', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G)
% 0.33/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('3', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.33/0.54      inference('split', [status(esa)], ['2'])).
% 0.33/0.54  thf('4', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)
% 0.33/0.54        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('5', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('6', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)
% 0.33/0.54        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.33/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.33/0.54  thf('7', plain,
% 0.33/0.54      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) | 
% 0.33/0.54       ~
% 0.33/0.54       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G))),
% 0.33/0.54      inference('split', [status(esa)], ['6'])).
% 0.33/0.54  thf('8', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G)
% 0.33/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('9', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('10', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G)
% 0.33/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.33/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.33/0.54  thf('11', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.33/0.54      inference('split', [status(esa)], ['10'])).
% 0.33/0.54  thf('12', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)
% 0.33/0.54        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('13', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('split', [status(esa)], ['12'])).
% 0.33/0.54  thf('14', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('15', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.33/0.54  thf('16', plain,
% 0.33/0.54      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) | 
% 0.33/0.54       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('sup-', [status(thm)], ['11', '15'])).
% 0.33/0.54  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('18', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('split', [status(esa)], ['2'])).
% 0.33/0.54  thf('19', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('20', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.33/0.54  thf('21', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t64_tmap_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54             ( l1_pre_topc @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.33/0.54                 ( m1_subset_1 @
% 0.33/0.54                   C @ 
% 0.33/0.54                   ( k1_zfmisc_1 @
% 0.33/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.33/0.54               ( ![D:$i]:
% 0.33/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.33/0.54                   ( ![E:$i]:
% 0.33/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.33/0.54                       ( ![F:$i]:
% 0.33/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                           ( ( ( ( E ) = ( F ) ) & 
% 0.33/0.54                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.33/0.54                             ( r1_tmap_1 @
% 0.33/0.54                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('22', plain,
% 0.33/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X13)
% 0.33/0.54          | ~ (v2_pre_topc @ X13)
% 0.33/0.54          | ~ (l1_pre_topc @ X13)
% 0.33/0.54          | (v2_struct_0 @ X14)
% 0.33/0.54          | ~ (m1_pre_topc @ X14 @ X13)
% 0.33/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.33/0.54          | (r1_tmap_1 @ X14 @ X16 @ (k2_tmap_1 @ X13 @ X16 @ X17 @ X14) @ X15)
% 0.33/0.54          | ((X18) != (X15))
% 0.33/0.54          | ~ (r1_tmap_1 @ X13 @ X16 @ X17 @ X18)
% 0.33/0.54          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X13))
% 0.33/0.54          | ~ (m1_subset_1 @ X17 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16))))
% 0.33/0.54          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16))
% 0.33/0.54          | ~ (v1_funct_1 @ X17)
% 0.33/0.54          | ~ (l1_pre_topc @ X16)
% 0.33/0.54          | ~ (v2_pre_topc @ X16)
% 0.33/0.54          | (v2_struct_0 @ X16))),
% 0.33/0.54      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.33/0.54  thf('23', plain,
% 0.33/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X16)
% 0.33/0.54          | ~ (v2_pre_topc @ X16)
% 0.33/0.54          | ~ (l1_pre_topc @ X16)
% 0.33/0.54          | ~ (v1_funct_1 @ X17)
% 0.33/0.54          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16))
% 0.33/0.54          | ~ (m1_subset_1 @ X17 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16))))
% 0.33/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.33/0.54          | ~ (r1_tmap_1 @ X13 @ X16 @ X17 @ X15)
% 0.33/0.54          | (r1_tmap_1 @ X14 @ X16 @ (k2_tmap_1 @ X13 @ X16 @ X17 @ X14) @ X15)
% 0.33/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.33/0.54          | ~ (m1_pre_topc @ X14 @ X13)
% 0.33/0.54          | (v2_struct_0 @ X14)
% 0.33/0.54          | ~ (l1_pre_topc @ X13)
% 0.33/0.54          | ~ (v2_pre_topc @ X13)
% 0.33/0.54          | (v2_struct_0 @ X13))),
% 0.33/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.33/0.54  thf('24', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.33/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ X0)
% 0.33/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.33/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.33/0.54             X1)
% 0.33/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.33/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54               (u1_struct_0 @ sk_A))
% 0.33/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.33/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.33/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.33/0.54          | (v2_struct_0 @ sk_A))),
% 0.33/0.54      inference('sup-', [status(thm)], ['21', '23'])).
% 0.33/0.54  thf('25', plain, ((v2_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('27', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('31', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ X0)
% 0.33/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.33/0.54          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.33/0.54             X1)
% 0.33/0.54          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.33/0.54          | (v2_struct_0 @ sk_A))),
% 0.33/0.54      inference('demod', [status(thm)],
% 0.33/0.54                ['24', '25', '26', '27', '28', '29', '30'])).
% 0.33/0.54  thf('32', plain,
% 0.33/0.54      ((![X0 : $i]:
% 0.33/0.54          ((v2_struct_0 @ sk_A)
% 0.33/0.54           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.33/0.54           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.33/0.54              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.33/0.54           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.33/0.54           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.33/0.54           | (v2_struct_0 @ X0)
% 0.33/0.54           | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['20', '31'])).
% 0.33/0.54  thf('33', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('34', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('35', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.33/0.54  thf('36', plain,
% 0.33/0.54      ((![X0 : $i]:
% 0.33/0.54          ((v2_struct_0 @ sk_A)
% 0.33/0.54           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.33/0.54              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.33/0.54           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.33/0.54           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.33/0.54           | (v2_struct_0 @ X0)
% 0.33/0.54           | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('demod', [status(thm)], ['32', '35'])).
% 0.33/0.54  thf('37', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.33/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)
% 0.33/0.54         | (v2_struct_0 @ sk_A)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['17', '36'])).
% 0.33/0.54  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('39', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B)
% 0.33/0.54         | (v2_struct_0 @ sk_D)
% 0.33/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)
% 0.33/0.54         | (v2_struct_0 @ sk_A)))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.33/0.54  thf('40', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G))
% 0.33/0.54         <= (~
% 0.33/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.33/0.54      inference('split', [status(esa)], ['12'])).
% 0.33/0.54  thf('41', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.33/0.54         <= (~
% 0.33/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.33/0.54  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('43', plain,
% 0.33/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.33/0.54         <= (~
% 0.33/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.33/0.54  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('45', plain,
% 0.33/0.54      (((v2_struct_0 @ sk_D))
% 0.33/0.54         <= (~
% 0.33/0.54             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ sk_G)) & 
% 0.33/0.54             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.33/0.54  thf('46', plain, (~ (v2_struct_0 @ sk_D)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('47', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G)) | 
% 0.33/0.54       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.33/0.54  thf('48', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G)) | 
% 0.33/0.54       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.33/0.54      inference('split', [status(esa)], ['10'])).
% 0.33/0.54  thf('49', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54         sk_G))),
% 0.33/0.54      inference('sat_resolution*', [status(thm)], ['7', '16', '47', '48'])).
% 0.33/0.54  thf('50', plain,
% 0.33/0.54      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.33/0.54        sk_G)),
% 0.33/0.54      inference('simpl_trail', [status(thm)], ['3', '49'])).
% 0.33/0.54  thf('51', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.33/0.54        (k1_zfmisc_1 @ 
% 0.33/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t65_tmap_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.33/0.54             ( l1_pre_topc @ B ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.33/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.33/0.54                 ( m1_subset_1 @
% 0.33/0.54                   C @ 
% 0.33/0.54                   ( k1_zfmisc_1 @
% 0.33/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.33/0.54               ( ![D:$i]:
% 0.33/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.33/0.54                   ( ![E:$i]:
% 0.33/0.54                     ( ( m1_subset_1 @
% 0.33/0.54                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.33/0.54                       ( ![F:$i]:
% 0.33/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.33/0.54                           ( ![G:$i]:
% 0.33/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.33/0.54                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.33/0.54                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.33/0.54                                   ( ( F ) = ( G ) ) ) =>
% 0.33/0.54                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.33/0.54                                   ( r1_tmap_1 @
% 0.33/0.54                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('52', plain,
% 0.33/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X19)
% 0.33/0.54          | ~ (v2_pre_topc @ X19)
% 0.33/0.54          | ~ (l1_pre_topc @ X19)
% 0.33/0.54          | (v2_struct_0 @ X20)
% 0.33/0.54          | ~ (m1_pre_topc @ X20 @ X19)
% 0.33/0.54          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.33/0.54          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X20))
% 0.33/0.54          | ~ (m1_connsp_2 @ X22 @ X19 @ X21)
% 0.33/0.54          | ((X21) != (X23))
% 0.33/0.54          | ~ (r1_tmap_1 @ X20 @ X24 @ (k2_tmap_1 @ X19 @ X24 @ X25 @ X20) @ 
% 0.33/0.54               X23)
% 0.33/0.54          | (r1_tmap_1 @ X19 @ X24 @ X25 @ X21)
% 0.33/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.33/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.33/0.54          | ~ (m1_subset_1 @ X25 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))))
% 0.33/0.54          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))
% 0.33/0.54          | ~ (v1_funct_1 @ X25)
% 0.33/0.54          | ~ (l1_pre_topc @ X24)
% 0.33/0.54          | ~ (v2_pre_topc @ X24)
% 0.33/0.54          | (v2_struct_0 @ X24))),
% 0.33/0.54      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.33/0.54  thf('53', plain,
% 0.33/0.54      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.33/0.54         ((v2_struct_0 @ X24)
% 0.33/0.54          | ~ (v2_pre_topc @ X24)
% 0.33/0.54          | ~ (l1_pre_topc @ X24)
% 0.33/0.54          | ~ (v1_funct_1 @ X25)
% 0.33/0.54          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))
% 0.33/0.54          | ~ (m1_subset_1 @ X25 @ 
% 0.33/0.54               (k1_zfmisc_1 @ 
% 0.33/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X24))))
% 0.33/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.33/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 0.33/0.54          | (r1_tmap_1 @ X19 @ X24 @ X25 @ X23)
% 0.33/0.54          | ~ (r1_tmap_1 @ X20 @ X24 @ (k2_tmap_1 @ X19 @ X24 @ X25 @ X20) @ 
% 0.33/0.54               X23)
% 0.33/0.54          | ~ (m1_connsp_2 @ X22 @ X19 @ X23)
% 0.33/0.54          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X20))
% 0.33/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.33/0.54          | ~ (m1_pre_topc @ X20 @ X19)
% 0.33/0.54          | (v2_struct_0 @ X20)
% 0.33/0.54          | ~ (l1_pre_topc @ X19)
% 0.33/0.54          | ~ (v2_pre_topc @ X19)
% 0.33/0.54          | (v2_struct_0 @ X19))),
% 0.33/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.33/0.54  thf('54', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.33/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ X0)
% 0.33/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.33/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.33/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.33/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.33/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.33/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.33/0.54               (u1_struct_0 @ sk_A))
% 0.33/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.33/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.33/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.33/0.54          | (v2_struct_0 @ sk_A))),
% 0.33/0.54      inference('sup-', [status(thm)], ['51', '53'])).
% 0.33/0.54  thf('55', plain, ((v2_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('57', plain,
% 0.33/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('58', plain, ((v1_funct_1 @ sk_C_1)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('61', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ X0)
% 0.33/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.33/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.33/0.54          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.33/0.54          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.33/0.54               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.33/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.33/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.33/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.54          | (v2_struct_0 @ sk_A))),
% 0.33/0.54      inference('demod', [status(thm)],
% 0.33/0.54                ['54', '55', '56', '57', '58', '59', '60'])).
% 0.33/0.54  thf('62', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_A)
% 0.33/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.54          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.33/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.33/0.54          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.33/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.33/0.54          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.33/0.54          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.33/0.54          | (v2_struct_0 @ sk_D)
% 0.33/0.54          | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['50', '61'])).
% 0.33/0.54  thf('63', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('64', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.33/0.54  thf('65', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('66', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_A)
% 0.33/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.54          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.33/0.54          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.33/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.33/0.54          | (v2_struct_0 @ sk_D)
% 0.33/0.54          | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.33/0.54  thf('67', plain,
% 0.33/0.54      (((v2_struct_0 @ sk_B)
% 0.33/0.54        | (v2_struct_0 @ sk_D)
% 0.33/0.54        | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))
% 0.33/0.54        | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.33/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.33/0.54        | (v2_struct_0 @ sk_A))),
% 0.33/0.54      inference('sup-', [status(thm)], ['1', '66'])).
% 0.33/0.54  thf('68', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('69', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('70', plain, (((sk_F) = (sk_G))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('71', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.33/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.33/0.54  thf('72', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('73', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(t56_tops_1, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( l1_pre_topc @ A ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.54               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.33/0.54                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('74', plain,
% 0.33/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.33/0.54          | ~ (v3_pre_topc @ X7 @ X8)
% 0.33/0.54          | ~ (r1_tarski @ X7 @ X9)
% 0.33/0.54          | (r1_tarski @ X7 @ (k1_tops_1 @ X8 @ X9))
% 0.33/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.33/0.54          | ~ (l1_pre_topc @ X8))),
% 0.33/0.54      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.33/0.54  thf('75', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         (~ (l1_pre_topc @ sk_B)
% 0.33/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.54          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.33/0.54          | ~ (r1_tarski @ sk_E @ X0)
% 0.33/0.54          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.33/0.54  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('77', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('78', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.54          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.33/0.54          | ~ (r1_tarski @ sk_E @ X0))),
% 0.33/0.54      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.33/0.54  thf('79', plain,
% 0.33/0.54      ((~ (r1_tarski @ sk_E @ sk_E)
% 0.33/0.54        | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['72', '78'])).
% 0.33/0.54  thf(d10_xboole_0, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.54  thf('80', plain,
% 0.33/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.33/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.54  thf('81', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.33/0.54      inference('simplify', [status(thm)], ['80'])).
% 0.33/0.54  thf('82', plain, ((r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.33/0.54      inference('demod', [status(thm)], ['79', '81'])).
% 0.33/0.54  thf(d3_tarski, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.33/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.33/0.54  thf('83', plain,
% 0.33/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.33/0.54          | (r2_hidden @ X0 @ X2)
% 0.33/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.33/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.33/0.54  thf('84', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.33/0.54          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.33/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.33/0.54  thf('85', plain, ((r2_hidden @ sk_G @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.33/0.54      inference('sup-', [status(thm)], ['71', '84'])).
% 0.33/0.54  thf('86', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(d1_connsp_2, axiom,
% 0.33/0.54    (![A:$i]:
% 0.33/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.54       ( ![B:$i]:
% 0.33/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.33/0.54           ( ![C:$i]:
% 0.33/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.33/0.54                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.33/0.54  thf('87', plain,
% 0.33/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.33/0.54          | ~ (r2_hidden @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.33/0.54          | (m1_connsp_2 @ X12 @ X11 @ X10)
% 0.33/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.33/0.54          | ~ (l1_pre_topc @ X11)
% 0.33/0.54          | ~ (v2_pre_topc @ X11)
% 0.33/0.54          | (v2_struct_0 @ X11))),
% 0.33/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.33/0.54  thf('88', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.33/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.33/0.54          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.33/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.33/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['86', '87'])).
% 0.33/0.54  thf('89', plain, ((v2_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('91', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((v2_struct_0 @ sk_B)
% 0.33/0.54          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.33/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.33/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.33/0.54  thf('92', plain,
% 0.33/0.54      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.33/0.54        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.33/0.54        | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['85', '91'])).
% 0.33/0.54  thf('93', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.33/0.54  thf('94', plain,
% 0.33/0.54      (((m1_connsp_2 @ sk_E @ sk_B @ sk_G) | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('demod', [status(thm)], ['92', '93'])).
% 0.33/0.54  thf('95', plain, (~ (v2_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('96', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.33/0.54      inference('clc', [status(thm)], ['94', '95'])).
% 0.33/0.54  thf('97', plain,
% 0.33/0.54      (((v2_struct_0 @ sk_B)
% 0.33/0.54        | (v2_struct_0 @ sk_D)
% 0.33/0.54        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.33/0.54        | (v2_struct_0 @ sk_A))),
% 0.33/0.54      inference('demod', [status(thm)], ['67', '68', '96'])).
% 0.33/0.54  thf('98', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.33/0.54  thf('99', plain,
% 0.33/0.54      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.33/0.54         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.33/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.33/0.54  thf('100', plain,
% 0.33/0.54      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.33/0.54         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.33/0.54      inference('split', [status(esa)], ['6'])).
% 0.33/0.54  thf('101', plain,
% 0.33/0.54      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) | 
% 0.33/0.54       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.33/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.33/0.54  thf('102', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.33/0.54      inference('sat_resolution*', [status(thm)], ['7', '16', '47', '101'])).
% 0.33/0.54  thf('103', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)),
% 0.33/0.54      inference('simpl_trail', [status(thm)], ['98', '102'])).
% 0.33/0.54  thf('104', plain,
% 0.33/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.33/0.54      inference('sup-', [status(thm)], ['97', '103'])).
% 0.33/0.54  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('106', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.33/0.54      inference('clc', [status(thm)], ['104', '105'])).
% 0.33/0.54  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('108', plain, ((v2_struct_0 @ sk_D)),
% 0.33/0.54      inference('clc', [status(thm)], ['106', '107'])).
% 0.33/0.54  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 0.33/0.54  
% 0.33/0.54  % SZS output end Refutation
% 0.33/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
