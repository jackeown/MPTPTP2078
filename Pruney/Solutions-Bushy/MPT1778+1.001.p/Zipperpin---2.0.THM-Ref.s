%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1778+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HtavDpRLE7

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:13 EST 2020

% Result     : Theorem 6.92s
% Output     : Refutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  213 (1338 expanded)
%              Number of leaves         :   27 ( 390 expanded)
%              Depth                    :   39
%              Number of atoms          : 3572 (65419 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   29 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t89_tmap_1,conjecture,(
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
                        & ( v5_pre_topc @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ D @ C )
                         => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t89_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X3 @ X5 @ X4 @ X2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X5 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t49_tmap_1,axiom,(
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
             => ( ( v5_pre_topc @ C @ B @ A )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ( v5_pre_topc @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X3 @ X5 @ X4 @ X2 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23','24','43','48','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X3 @ X5 @ X4 @ X2 @ X6 ) @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['55','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['55','74'])).

thf(t15_tmap_1,axiom,(
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
             => ( ( m1_pre_topc @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ? [E: $i] :
                        ( ( E = D )
                        & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( ( sk_E @ X12 @ X11 )
        = X12 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t15_tmap_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X1 )
        = ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X1 )
        = ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X0 )
        = ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X0 )
        = ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_C )
    | ( ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ sk_C )
      = ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_D_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ sk_C )
      = ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['55','74'])).

thf('92',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_E @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t15_tmap_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_D_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('105',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v5_pre_topc @ X14 @ X13 @ X15 )
      | ( r1_tmap_1 @ X13 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E_1 @ X0 )
      | ~ ( v5_pre_topc @ sk_E_1 @ sk_C @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v5_pre_topc @ sk_E_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('120',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E_1 @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112','117','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['104','124'])).

thf('126',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ sk_E_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('128',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X18 @ X21 )
      | ~ ( r1_tmap_1 @ X21 @ X17 @ X22 @ X20 )
      | ( X20 != X23 )
      | ( r1_tmap_1 @ X18 @ X17 @ ( k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('129',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ( r1_tmap_1 @ X18 @ X17 @ ( k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22 ) @ X23 )
      | ~ ( r1_tmap_1 @ X21 @ X17 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E_1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E_1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E_1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_C )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['75','139'])).

thf('141',plain,(
    m1_pre_topc @ sk_D_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('151',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( r1_tmap_1 @ X13 @ X15 @ X14 @ ( sk_D @ X14 @ X13 @ X15 ) )
      | ( v5_pre_topc @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('156',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf('157',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','157'])).

thf('159',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['149','160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['163'])).

thf('165',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('166',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['163'])).

thf('167',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['163'])).

thf('170',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('172',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['163'])).

thf('173',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['163'])).

thf('175',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['167','170','173','174'])).

thf('176',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 @ sk_E_1 ) @ sk_D_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['164','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['0','183'])).


%------------------------------------------------------------------------------
