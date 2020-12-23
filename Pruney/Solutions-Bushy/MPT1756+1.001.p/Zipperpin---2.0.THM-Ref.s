%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1756+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Loi9FWXUui

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 314 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   22
%              Number of atoms          : 1465 (12519 expanded)
%              Number of equality atoms :   12 ( 163 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_tmap_1 @ X4 @ X6 @ ( k2_tmap_1 @ X3 @ X6 @ X7 @ X4 ) @ X5 )
      | ( X8 != X5 )
      | ~ ( r1_tmap_1 @ X3 @ X6 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X6 @ X7 @ X5 )
      | ( r1_tmap_1 @ X4 @ X6 @ ( k2_tmap_1 @ X3 @ X6 @ X7 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_tarski @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_connsp_2 @ X12 @ X9 @ X11 )
      | ( X11 != X13 )
      | ~ ( r1_tmap_1 @ X10 @ X14 @ ( k2_tmap_1 @ X9 @ X14 @ X15 @ X10 ) @ X13 )
      | ( r1_tmap_1 @ X9 @ X14 @ X15 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r1_tmap_1 @ X9 @ X14 @ X15 @ X13 )
      | ~ ( r1_tmap_1 @ X10 @ X14 @ ( k2_tmap_1 @ X9 @ X14 @ X15 @ X10 ) @ X13 )
      | ~ ( m1_connsp_2 @ X12 @ X9 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( m1_connsp_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_G @ sk_E )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','76'])).

thf('78',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['32'])).

thf('79',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['7','40','85'])).

thf('87',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['80','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).


%------------------------------------------------------------------------------
