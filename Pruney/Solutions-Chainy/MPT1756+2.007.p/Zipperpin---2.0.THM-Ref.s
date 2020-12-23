%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BRPFgxA4fT

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:51 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 498 expanded)
%              Number of leaves         :   31 ( 152 expanded)
%              Depth                    :   28
%              Number of atoms          : 1885 (18663 expanded)
%              Number of equality atoms :   11 ( 235 expanded)
%              Maximal formula depth    :   28 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X17 )
      | ( X17 != X19 )
      | ~ ( r1_tmap_1 @ X15 @ X20 @ X21 @ X17 )
      | ( r1_tmap_1 @ X16 @ X20 @ ( k2_tmap_1 @ X15 @ X20 @ X21 @ X16 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( r1_tmap_1 @ X16 @ X20 @ ( k2_tmap_1 @ X15 @ X20 @ X21 @ X16 ) @ X19 )
      | ~ ( r1_tmap_1 @ X15 @ X20 @ X21 @ X19 )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X19 )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k1_tops_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_E )
    | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_G @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ ( k1_tops_1 @ X8 @ X9 ) )
      | ( m1_connsp_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('61',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['30','33','63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['12','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('79',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['11','77','78'])).

thf('80',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['7','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X17 )
      | ( X17 != X19 )
      | ~ ( r1_tmap_1 @ X16 @ X20 @ ( k2_tmap_1 @ X15 @ X20 @ X21 @ X16 ) @ X19 )
      | ( r1_tmap_1 @ X15 @ X20 @ X21 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('83',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( r1_tmap_1 @ X15 @ X20 @ X21 @ X19 )
      | ~ ( r1_tmap_1 @ X16 @ X20 @ ( k2_tmap_1 @ X15 @ X20 @ X21 @ X16 ) @ X19 )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X19 )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
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
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
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
    inference(demod,[status(thm)],['84','85','86','87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('95',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('99',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['34','35'])).

thf('100',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('102',plain,
    ( ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    r2_hidden @ sk_G @ ( k1_tops_1 @ sk_B @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['99','106'])).

thf('108',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('109',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ ( k1_tops_1 @ X8 @ X9 ) )
      | ( m1_connsp_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('116',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','118'])).

thf('120',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['69'])).

thf('121',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('124',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('127',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['11','77','127'])).

thf('129',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['122','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['0','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BRPFgxA4fT
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 299 iterations in 0.141s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.59  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.37/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.37/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.59  thf(t66_tmap_1, conjecture,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.59             ( l1_pre_topc @ B ) ) =>
% 0.37/0.59           ( ![C:$i]:
% 0.37/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.59                 ( m1_subset_1 @
% 0.37/0.59                   C @ 
% 0.37/0.59                   ( k1_zfmisc_1 @
% 0.37/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.59               ( ![D:$i]:
% 0.37/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.59                   ( ![E:$i]:
% 0.37/0.59                     ( ( m1_subset_1 @
% 0.37/0.59                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.59                       ( ![F:$i]:
% 0.37/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.59                           ( ![G:$i]:
% 0.37/0.59                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.59                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.37/0.59                                   ( r2_hidden @ F @ E ) & 
% 0.37/0.59                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.37/0.59                                   ( ( F ) = ( G ) ) ) =>
% 0.37/0.59                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.37/0.59                                   ( r1_tmap_1 @
% 0.37/0.59                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i]:
% 0.37/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.59            ( l1_pre_topc @ A ) ) =>
% 0.37/0.59          ( ![B:$i]:
% 0.37/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.59                ( l1_pre_topc @ B ) ) =>
% 0.37/0.59              ( ![C:$i]:
% 0.37/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.59                    ( v1_funct_2 @
% 0.37/0.59                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.59                    ( m1_subset_1 @
% 0.37/0.59                      C @ 
% 0.37/0.59                      ( k1_zfmisc_1 @
% 0.37/0.59                        ( k2_zfmisc_1 @
% 0.37/0.59                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.59                  ( ![D:$i]:
% 0.37/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.59                      ( ![E:$i]:
% 0.37/0.59                        ( ( m1_subset_1 @
% 0.37/0.59                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.59                          ( ![F:$i]:
% 0.37/0.59                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.59                              ( ![G:$i]:
% 0.37/0.59                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.59                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.37/0.59                                      ( r2_hidden @ F @ E ) & 
% 0.37/0.59                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.37/0.59                                      ( ( F ) = ( G ) ) ) =>
% 0.37/0.59                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.37/0.59                                      ( r1_tmap_1 @
% 0.37/0.59                                        D @ A @ 
% 0.37/0.59                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.37/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t1_tsep_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( l1_pre_topc @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.59           ( m1_subset_1 @
% 0.37/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i]:
% 0.37/0.59         (~ (m1_pre_topc @ X13 @ X14)
% 0.37/0.59          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.37/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.59          | ~ (l1_pre_topc @ X14))),
% 0.37/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf('4', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.37/0.59      inference('split', [status(esa)], ['6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('9', plain, (((sk_F) = (sk_G))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.37/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)) | 
% 0.37/0.59       ~
% 0.37/0.59       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.37/0.59      inference('split', [status(esa)], ['10'])).
% 0.37/0.59  thf('12', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('14', plain, (((sk_F) = (sk_G))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.37/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('split', [status(esa)], ['15'])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.59        (k1_zfmisc_1 @ 
% 0.37/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t65_tmap_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.37/0.59             ( l1_pre_topc @ B ) ) =>
% 0.37/0.59           ( ![C:$i]:
% 0.37/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.37/0.59                 ( m1_subset_1 @
% 0.37/0.59                   C @ 
% 0.37/0.59                   ( k1_zfmisc_1 @
% 0.37/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.37/0.59               ( ![D:$i]:
% 0.37/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.37/0.59                   ( ![E:$i]:
% 0.37/0.59                     ( ( m1_subset_1 @
% 0.37/0.59                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.59                       ( ![F:$i]:
% 0.37/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.59                           ( ![G:$i]:
% 0.37/0.59                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.37/0.59                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.37/0.59                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.37/0.59                                   ( ( F ) = ( G ) ) ) =>
% 0.37/0.59                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.37/0.59                                   ( r1_tmap_1 @
% 0.37/0.59                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.59         ((v2_struct_0 @ X15)
% 0.37/0.59          | ~ (v2_pre_topc @ X15)
% 0.37/0.59          | ~ (l1_pre_topc @ X15)
% 0.37/0.59          | (v2_struct_0 @ X16)
% 0.37/0.59          | ~ (m1_pre_topc @ X16 @ X15)
% 0.37/0.59          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.37/0.59          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X16))
% 0.37/0.59          | ~ (m1_connsp_2 @ X18 @ X15 @ X17)
% 0.37/0.59          | ((X17) != (X19))
% 0.37/0.59          | ~ (r1_tmap_1 @ X15 @ X20 @ X21 @ X17)
% 0.37/0.59          | (r1_tmap_1 @ X16 @ X20 @ (k2_tmap_1 @ X15 @ X20 @ X21 @ X16) @ X19)
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.37/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.59          | ~ (m1_subset_1 @ X21 @ 
% 0.37/0.59               (k1_zfmisc_1 @ 
% 0.37/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))))
% 0.37/0.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))
% 0.37/0.59          | ~ (v1_funct_1 @ X21)
% 0.37/0.59          | ~ (l1_pre_topc @ X20)
% 0.37/0.59          | ~ (v2_pre_topc @ X20)
% 0.37/0.59          | (v2_struct_0 @ X20))),
% 0.37/0.59      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.59         ((v2_struct_0 @ X20)
% 0.37/0.59          | ~ (v2_pre_topc @ X20)
% 0.37/0.59          | ~ (l1_pre_topc @ X20)
% 0.37/0.59          | ~ (v1_funct_1 @ X21)
% 0.37/0.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))
% 0.37/0.59          | ~ (m1_subset_1 @ X21 @ 
% 0.37/0.59               (k1_zfmisc_1 @ 
% 0.37/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))))
% 0.37/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.37/0.59          | (r1_tmap_1 @ X16 @ X20 @ (k2_tmap_1 @ X15 @ X20 @ X21 @ X16) @ X19)
% 0.37/0.59          | ~ (r1_tmap_1 @ X15 @ X20 @ X21 @ X19)
% 0.37/0.59          | ~ (m1_connsp_2 @ X18 @ X15 @ X19)
% 0.37/0.59          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X16))
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.37/0.59          | ~ (m1_pre_topc @ X16 @ X15)
% 0.37/0.59          | (v2_struct_0 @ X16)
% 0.37/0.59          | ~ (l1_pre_topc @ X15)
% 0.37/0.59          | ~ (v2_pre_topc @ X15)
% 0.37/0.59          | (v2_struct_0 @ X15))),
% 0.37/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | (v2_struct_0 @ X0)
% 0.37/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.37/0.59          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.37/0.59             X1)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.59               (u1_struct_0 @ sk_A))
% 0.37/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.59          | (v2_struct_0 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '20'])).
% 0.37/0.59  thf('22', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('25', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | (v2_struct_0 @ X0)
% 0.37/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.37/0.59          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.37/0.59             X1)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (v2_struct_0 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)],
% 0.37/0.59                ['21', '22', '23', '24', '25', '26', '27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_A)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.37/0.59             X1)
% 0.37/0.59          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.59          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X1)
% 0.37/0.59          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59          | (v2_struct_0 @ X0)
% 0.37/0.59          | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['17', '28'])).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      ((![X0 : $i]:
% 0.37/0.59          ((v2_struct_0 @ sk_B)
% 0.37/0.59           | (v2_struct_0 @ X0)
% 0.37/0.59           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.37/0.59           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.37/0.59           | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.37/0.59           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.59              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.37/0.59           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.37/0.59           | (v2_struct_0 @ sk_A)))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['16', '29'])).
% 0.37/0.59  thf('31', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('32', plain, (((sk_F) = (sk_G))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('33', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.59  thf('34', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('35', plain, (((sk_F) = (sk_G))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('36', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.37/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t56_tops_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( l1_pre_topc @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.59           ( ![C:$i]:
% 0.37/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.59               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.59                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.37/0.59          | ~ (v3_pre_topc @ X4 @ X5)
% 0.37/0.59          | ~ (r1_tarski @ X4 @ X6)
% 0.37/0.59          | (r1_tarski @ X4 @ (k1_tops_1 @ X5 @ X6))
% 0.37/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.37/0.59          | ~ (l1_pre_topc @ X5))),
% 0.37/0.59      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59          | ~ (r1_tarski @ sk_E @ X0)
% 0.37/0.59          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.59  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('42', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59          | ~ (r1_tarski @ sk_E @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      ((~ (r1_tarski @ sk_E @ sk_E)
% 0.37/0.59        | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['37', '43'])).
% 0.37/0.59  thf(d3_tarski, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      (![X1 : $i, X3 : $i]:
% 0.37/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.59  thf('46', plain,
% 0.37/0.59      (![X1 : $i, X3 : $i]:
% 0.37/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.59  thf('47', plain,
% 0.37/0.59      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.59  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.37/0.59  thf('49', plain, ((r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.37/0.59      inference('demod', [status(thm)], ['44', '48'])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.59          | (r2_hidden @ X0 @ X2)
% 0.37/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.59  thf('51', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.37/0.59          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.37/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.59  thf('52', plain, ((r2_hidden @ sk_G @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '51'])).
% 0.37/0.59  thf('53', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d1_connsp_2, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.59           ( ![C:$i]:
% 0.37/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.59               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.37/0.59                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.37/0.59          | ~ (r2_hidden @ X7 @ (k1_tops_1 @ X8 @ X9))
% 0.37/0.59          | (m1_connsp_2 @ X9 @ X8 @ X7)
% 0.37/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.37/0.59          | ~ (l1_pre_topc @ X8)
% 0.37/0.59          | ~ (v2_pre_topc @ X8)
% 0.37/0.59          | (v2_struct_0 @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.37/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.59  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('58', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.37/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.37/0.59  thf('59', plain,
% 0.37/0.59      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.37/0.59        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.37/0.59        | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['52', '58'])).
% 0.37/0.59  thf('60', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.59  thf('61', plain,
% 0.37/0.59      (((m1_connsp_2 @ sk_E @ sk_B @ sk_G) | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.59  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('63', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.37/0.59      inference('clc', [status(thm)], ['61', '62'])).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      ((![X0 : $i]:
% 0.37/0.59          ((v2_struct_0 @ sk_B)
% 0.37/0.59           | (v2_struct_0 @ X0)
% 0.37/0.59           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.37/0.59           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.59              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_G)
% 0.37/0.59           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.37/0.59           | (v2_struct_0 @ sk_A)))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('demod', [status(thm)], ['30', '33', '63'])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      ((((v2_struct_0 @ sk_A)
% 0.37/0.59         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.37/0.59         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.37/0.59         | (v2_struct_0 @ sk_D_1)
% 0.37/0.59         | (v2_struct_0 @ sk_B)))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['12', '64'])).
% 0.37/0.59  thf('66', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('67', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('68', plain,
% 0.37/0.59      ((((v2_struct_0 @ sk_A)
% 0.37/0.59         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59         | (v2_struct_0 @ sk_D_1)
% 0.37/0.59         | (v2_struct_0 @ sk_B)))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.59  thf('69', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)
% 0.37/0.59        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('70', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))
% 0.37/0.59         <= (~
% 0.37/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)))),
% 0.37/0.59      inference('split', [status(esa)], ['69'])).
% 0.37/0.59  thf('71', plain,
% 0.37/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_A)))
% 0.37/0.59         <= (~
% 0.37/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.37/0.59             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['68', '70'])).
% 0.37/0.59  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('73', plain,
% 0.37/0.59      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1)))
% 0.37/0.59         <= (~
% 0.37/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.37/0.59             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('clc', [status(thm)], ['71', '72'])).
% 0.37/0.59  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('75', plain,
% 0.37/0.59      (((v2_struct_0 @ sk_D_1))
% 0.37/0.59         <= (~
% 0.37/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) & 
% 0.37/0.59             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('clc', [status(thm)], ['73', '74'])).
% 0.37/0.59  thf('76', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('77', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.37/0.59       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.37/0.59      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.59  thf('78', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)) | 
% 0.37/0.59       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.37/0.59      inference('split', [status(esa)], ['15'])).
% 0.37/0.59  thf('79', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['11', '77', '78'])).
% 0.37/0.59  thf('80', plain,
% 0.37/0.59      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.37/0.59        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_G)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['7', '79'])).
% 0.37/0.59  thf('81', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.59        (k1_zfmisc_1 @ 
% 0.37/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('82', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.59         ((v2_struct_0 @ X15)
% 0.37/0.59          | ~ (v2_pre_topc @ X15)
% 0.37/0.59          | ~ (l1_pre_topc @ X15)
% 0.37/0.59          | (v2_struct_0 @ X16)
% 0.37/0.59          | ~ (m1_pre_topc @ X16 @ X15)
% 0.37/0.59          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.37/0.59          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X16))
% 0.37/0.59          | ~ (m1_connsp_2 @ X18 @ X15 @ X17)
% 0.37/0.59          | ((X17) != (X19))
% 0.37/0.59          | ~ (r1_tmap_1 @ X16 @ X20 @ (k2_tmap_1 @ X15 @ X20 @ X21 @ X16) @ 
% 0.37/0.59               X19)
% 0.37/0.59          | (r1_tmap_1 @ X15 @ X20 @ X21 @ X17)
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.37/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.59          | ~ (m1_subset_1 @ X21 @ 
% 0.37/0.59               (k1_zfmisc_1 @ 
% 0.37/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))))
% 0.37/0.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))
% 0.37/0.59          | ~ (v1_funct_1 @ X21)
% 0.37/0.59          | ~ (l1_pre_topc @ X20)
% 0.37/0.59          | ~ (v2_pre_topc @ X20)
% 0.37/0.59          | (v2_struct_0 @ X20))),
% 0.37/0.59      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.37/0.59  thf('83', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.59         ((v2_struct_0 @ X20)
% 0.37/0.59          | ~ (v2_pre_topc @ X20)
% 0.37/0.59          | ~ (l1_pre_topc @ X20)
% 0.37/0.59          | ~ (v1_funct_1 @ X21)
% 0.37/0.59          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))
% 0.37/0.59          | ~ (m1_subset_1 @ X21 @ 
% 0.37/0.59               (k1_zfmisc_1 @ 
% 0.37/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X20))))
% 0.37/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.37/0.59          | (r1_tmap_1 @ X15 @ X20 @ X21 @ X19)
% 0.37/0.59          | ~ (r1_tmap_1 @ X16 @ X20 @ (k2_tmap_1 @ X15 @ X20 @ X21 @ X16) @ 
% 0.37/0.59               X19)
% 0.37/0.59          | ~ (m1_connsp_2 @ X18 @ X15 @ X19)
% 0.37/0.59          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X16))
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.37/0.59          | ~ (m1_pre_topc @ X16 @ X15)
% 0.37/0.59          | (v2_struct_0 @ X16)
% 0.37/0.59          | ~ (l1_pre_topc @ X15)
% 0.37/0.59          | ~ (v2_pre_topc @ X15)
% 0.37/0.59          | (v2_struct_0 @ X15))),
% 0.37/0.59      inference('simplify', [status(thm)], ['82'])).
% 0.37/0.59  thf('84', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | (v2_struct_0 @ X0)
% 0.37/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.37/0.59          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.37/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.59               (u1_struct_0 @ sk_A))
% 0.37/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.59          | (v2_struct_0 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['81', '83'])).
% 0.37/0.59  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('87', plain,
% 0.37/0.59      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('88', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('91', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | (v2_struct_0 @ X0)
% 0.37/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.37/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.37/0.59          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.37/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.37/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.37/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.37/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (v2_struct_0 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)],
% 0.37/0.59                ['84', '85', '86', '87', '88', '89', '90'])).
% 0.37/0.59  thf('92', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_A)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))
% 0.37/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.37/0.59          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.37/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.59          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.37/0.59          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.37/0.59          | (v2_struct_0 @ sk_D_1)
% 0.37/0.59          | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['80', '91'])).
% 0.37/0.59  thf('93', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('94', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.59  thf('95', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('96', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_A)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.37/0.59          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.37/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.37/0.59          | (v2_struct_0 @ sk_D_1)
% 0.37/0.59          | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.37/0.59  thf('97', plain,
% 0.37/0.59      (((v2_struct_0 @ sk_B)
% 0.37/0.59        | (v2_struct_0 @ sk_D_1)
% 0.37/0.59        | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_D_1))
% 0.37/0.59        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_G)
% 0.37/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.37/0.59        | (v2_struct_0 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '96'])).
% 0.37/0.59  thf('98', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.37/0.59  thf('99', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.37/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.59  thf('100', plain,
% 0.37/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.59  thf('101', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59          | ~ (r1_tarski @ sk_E @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.37/0.59  thf('102', plain,
% 0.37/0.59      ((~ (r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.37/0.59        | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ (u1_struct_0 @ sk_D_1))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['100', '101'])).
% 0.37/0.59  thf('103', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('104', plain,
% 0.37/0.59      ((r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.59      inference('demod', [status(thm)], ['102', '103'])).
% 0.37/0.59  thf('105', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.59          | (r2_hidden @ X0 @ X2)
% 0.37/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.59  thf('106', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ (u1_struct_0 @ sk_D_1)))
% 0.37/0.59          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.37/0.59      inference('sup-', [status(thm)], ['104', '105'])).
% 0.37/0.59  thf('107', plain,
% 0.37/0.59      ((r2_hidden @ sk_G @ (k1_tops_1 @ sk_B @ (u1_struct_0 @ sk_D_1)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['99', '106'])).
% 0.37/0.59  thf('108', plain,
% 0.37/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.59  thf('109', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.37/0.59          | ~ (r2_hidden @ X7 @ (k1_tops_1 @ X8 @ X9))
% 0.37/0.59          | (m1_connsp_2 @ X9 @ X8 @ X7)
% 0.37/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.37/0.59          | ~ (l1_pre_topc @ X8)
% 0.37/0.59          | ~ (v2_pre_topc @ X8)
% 0.37/0.59          | (v2_struct_0 @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.37/0.59  thf('110', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.37/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ (u1_struct_0 @ sk_D_1)))
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['108', '109'])).
% 0.37/0.59  thf('111', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('113', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v2_struct_0 @ sk_B)
% 0.37/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.37/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ (u1_struct_0 @ sk_D_1)))
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.37/0.59  thf('114', plain,
% 0.37/0.59      ((~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.37/0.59        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_G)
% 0.37/0.59        | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['107', '113'])).
% 0.37/0.59  thf('115', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.59  thf('116', plain,
% 0.37/0.59      (((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_G)
% 0.37/0.59        | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['114', '115'])).
% 0.37/0.59  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('118', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_G)),
% 0.37/0.59      inference('clc', [status(thm)], ['116', '117'])).
% 0.37/0.59  thf('119', plain,
% 0.37/0.59      (((v2_struct_0 @ sk_B)
% 0.37/0.59        | (v2_struct_0 @ sk_D_1)
% 0.37/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)
% 0.37/0.59        | (v2_struct_0 @ sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['97', '98', '118'])).
% 0.37/0.59  thf('120', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.37/0.59         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.37/0.59      inference('split', [status(esa)], ['69'])).
% 0.37/0.59  thf('121', plain, (((sk_F) = (sk_G))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('122', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.37/0.59         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.37/0.59      inference('demod', [status(thm)], ['120', '121'])).
% 0.37/0.59  thf('123', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.37/0.59      inference('split', [status(esa)], ['6'])).
% 0.37/0.59  thf('124', plain, (((sk_F) = (sk_G))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('125', plain,
% 0.37/0.59      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.37/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)))),
% 0.37/0.59      inference('demod', [status(thm)], ['123', '124'])).
% 0.37/0.59  thf('126', plain,
% 0.37/0.59      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))
% 0.37/0.59         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)))),
% 0.37/0.59      inference('split', [status(esa)], ['10'])).
% 0.37/0.59  thf('127', plain,
% 0.37/0.59      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F)) | 
% 0.37/0.59       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G))),
% 0.37/0.59      inference('sup-', [status(thm)], ['125', '126'])).
% 0.37/0.59  thf('128', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_F))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['11', '77', '127'])).
% 0.37/0.59  thf('129', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_G)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['122', '128'])).
% 0.37/0.59  thf('130', plain,
% 0.37/0.59      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['119', '129'])).
% 0.37/0.59  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('132', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.37/0.59      inference('clc', [status(thm)], ['130', '131'])).
% 0.37/0.59  thf('133', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('134', plain, ((v2_struct_0 @ sk_D_1)),
% 0.37/0.59      inference('clc', [status(thm)], ['132', '133'])).
% 0.37/0.59  thf('135', plain, ($false), inference('demod', [status(thm)], ['0', '134'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
