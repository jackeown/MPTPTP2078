%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.crGLhgkqmi

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:08 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  344 (5392 expanded)
%              Number of leaves         :   30 (1576 expanded)
%              Depth                    :   33
%              Number of atoms          : 4714 (202408 expanded)
%              Number of equality atoms :   81 ( 595 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t79_tmap_1,conjecture,(
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
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ D @ C )
                          & ( m1_pre_topc @ E @ D ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) )).

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
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( m1_pre_topc @ D @ C )
                            & ( m1_pre_topc @ E @ D ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('5',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X20 @ ( k3_tmap_1 @ X22 @ X19 @ X21 @ X21 @ X20 ) )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_F ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('20',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ( ( k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) @ X12 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('31',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( k2_tmap_1 @ X6 @ X4 @ X7 @ X5 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('47',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('48',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('66',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['13','18','64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) @ ( k3_tmap_1 @ X25 @ X23 @ X27 @ X24 @ X26 ) @ ( k2_tmap_1 @ X25 @ X23 @ X28 @ X24 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_tmap_1 @ X25 @ X23 @ X28 @ X27 ) )
      | ~ ( m1_pre_topc @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_C )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_C ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X2 @ sk_F ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_C )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_C ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X2 @ sk_F ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('86',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('112',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('121',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('122',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('130',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) @ ( k3_tmap_1 @ X25 @ X23 @ X27 @ X24 @ X26 ) @ ( k2_tmap_1 @ X25 @ X23 @ X28 @ X24 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_tmap_1 @ X25 @ X23 @ X28 @ X27 ) )
      | ~ ( m1_pre_topc @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('135',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('145',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('146',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','147'])).

thf('149',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('150',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('157',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['156','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('167',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('168',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['155','169'])).

thf('171',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('172',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','154','176','177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','179'])).

thf('181',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('186',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184','185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','188'])).

thf('190',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('192',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_pre_topc @ X31 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('195',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['190','196'])).

thf('199',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('201',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ( ( k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) @ X12 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('207',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('208',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('209',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('210',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('211',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','206','207','208','209','210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','212'])).

thf('214',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('215',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['198','216'])).

thf('218',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('220',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( k2_tmap_1 @ X6 @ X4 @ X7 @ X5 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('224',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('230',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','227','232','233','234'])).

thf('236',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('237',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('238',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('239',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('240',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('241',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['235','236','237','238','239','240','241'])).

thf('243',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['218','242'])).

thf('244',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['217','247','248'])).

thf('250',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['189','197','253'])).

thf('255',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['259','260','261'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['256','262'])).

thf('264',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('265',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['266','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['255','270'])).

thf('272',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['259','260','261'])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['190','196'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51'])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['277','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['190','196'])).

thf('283',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['274','281','282'])).

thf('284',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['283','284'])).

thf('286',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('288',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['271','287'])).

thf('289',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','206','207','208','209','210','211'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['289','295'])).

thf('297',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('298',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['299','300'])).

thf('302',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['301','302'])).

thf('304',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['288','303'])).

thf('305',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['254','304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['309','310'])).

thf('312',plain,(
    $false ),
    inference(demod,[status(thm)],['0','311'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.crGLhgkqmi
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:27:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 748 iterations in 0.524s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(sk_E_type, type, sk_E: $i).
% 0.76/0.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.98  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.76/0.98  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.76/0.98  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.76/0.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.98  thf(sk_F_type, type, sk_F: $i).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(t79_tmap_1, conjecture,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.99                   ( ![E:$i]:
% 0.76/0.99                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.76/0.99                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.76/0.99                         ( ![F:$i]:
% 0.76/0.99                           ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.99                               ( v1_funct_2 @
% 0.76/0.99                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                               ( m1_subset_1 @
% 0.76/0.99                                 F @ 
% 0.76/0.99                                 ( k1_zfmisc_1 @
% 0.76/0.99                                   ( k2_zfmisc_1 @
% 0.76/0.99                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                             ( r2_funct_2 @
% 0.76/0.99                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.99                               ( k3_tmap_1 @
% 0.76/0.99                                 A @ B @ D @ E @ 
% 0.76/0.99                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.76/0.99                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i]:
% 0.76/0.99        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.99            ( l1_pre_topc @ A ) ) =>
% 0.76/0.99          ( ![B:$i]:
% 0.76/0.99            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99                ( l1_pre_topc @ B ) ) =>
% 0.76/0.99              ( ![C:$i]:
% 0.76/0.99                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.99                  ( ![D:$i]:
% 0.76/0.99                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.99                      ( ![E:$i]:
% 0.76/0.99                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.76/0.99                          ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.76/0.99                            ( ![F:$i]:
% 0.76/0.99                              ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.99                                  ( v1_funct_2 @
% 0.76/0.99                                    F @ ( u1_struct_0 @ C ) @ 
% 0.76/0.99                                    ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                                  ( m1_subset_1 @
% 0.76/0.99                                    F @ 
% 0.76/0.99                                    ( k1_zfmisc_1 @
% 0.76/0.99                                      ( k2_zfmisc_1 @
% 0.76/0.99                                        ( u1_struct_0 @ C ) @ 
% 0.76/0.99                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                                ( r2_funct_2 @
% 0.76/0.99                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.99                                  ( k3_tmap_1 @
% 0.76/0.99                                    A @ B @ D @ E @ 
% 0.76/0.99                                    ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.76/0.99                                  ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t79_tmap_1])).
% 0.76/0.99  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t2_tsep_1, axiom,
% 0.76/0.99    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('4', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('5', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t74_tmap_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( ( v1_funct_1 @ D ) & 
% 0.76/0.99                     ( v1_funct_2 @
% 0.76/0.99                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                     ( m1_subset_1 @
% 0.76/0.99                       D @ 
% 0.76/0.99                       ( k1_zfmisc_1 @
% 0.76/0.99                         ( k2_zfmisc_1 @
% 0.76/0.99                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                   ( r2_funct_2 @
% 0.76/0.99                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.76/0.99                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X19)
% 0.76/0.99          | ~ (v2_pre_topc @ X19)
% 0.76/0.99          | ~ (l1_pre_topc @ X19)
% 0.76/0.99          | ~ (v1_funct_1 @ X20)
% 0.76/0.99          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.76/0.99          | ~ (m1_subset_1 @ X20 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ X20 @ 
% 0.76/0.99             (k3_tmap_1 @ X22 @ X19 @ X21 @ X21 @ X20))
% 0.76/0.99          | ~ (m1_pre_topc @ X21 @ X22)
% 0.76/0.99          | (v2_struct_0 @ X21)
% 0.76/0.99          | ~ (l1_pre_topc @ X22)
% 0.76/0.99          | ~ (v2_pre_topc @ X22)
% 0.76/0.99          | (v2_struct_0 @ X22))),
% 0.76/0.99      inference('cnf', [status(esa)], [t74_tmap_1])).
% 0.76/0.99  thf('7', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_F))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.99  thf('8', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('9', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('11', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('12', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_F))
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.76/0.99  thf('13', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99           (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99        | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['4', '12'])).
% 0.76/0.99  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(dt_m1_pre_topc, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_pre_topc @ A ) =>
% 0.76/0.99       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      (![X2 : $i, X3 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.76/0.99  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.99  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('18', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('19', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('21', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(d5_tmap_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( m1_pre_topc @ C @ A ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( m1_pre_topc @ D @ A ) =>
% 0.76/0.99                   ( ![E:$i]:
% 0.76/0.99                     ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.99                         ( v1_funct_2 @
% 0.76/0.99                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                         ( m1_subset_1 @
% 0.76/0.99                           E @ 
% 0.76/0.99                           ( k1_zfmisc_1 @
% 0.76/0.99                             ( k2_zfmisc_1 @
% 0.76/0.99                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                       ( ( m1_pre_topc @ D @ C ) =>
% 0.76/0.99                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.76/0.99                           ( k2_partfun1 @
% 0.76/0.99                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.76/0.99                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('22', plain,
% 0.76/0.99      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X8)
% 0.76/0.99          | ~ (v2_pre_topc @ X8)
% 0.76/0.99          | ~ (l1_pre_topc @ X8)
% 0.76/0.99          | ~ (m1_pre_topc @ X9 @ X10)
% 0.76/0.99          | ~ (m1_pre_topc @ X9 @ X11)
% 0.76/0.99          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.76/0.99                 X12 @ (u1_struct_0 @ X9)))
% 0.76/0.99          | ~ (m1_subset_1 @ X12 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.76/0.99          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.76/0.99          | ~ (v1_funct_1 @ X12)
% 0.76/0.99          | ~ (m1_pre_topc @ X11 @ X10)
% 0.76/0.99          | ~ (l1_pre_topc @ X10)
% 0.76/0.99          | ~ (v2_pre_topc @ X10)
% 0.76/0.99          | (v2_struct_0 @ X10))),
% 0.76/0.99      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.99  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('25', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('28', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['20', '28'])).
% 0.76/0.99  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(cc1_pre_topc, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.76/0.99  thf('33', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X0 @ X1)
% 0.76/0.99          | (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.99  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('37', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('38', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['29', '30', '31', '37'])).
% 0.76/0.99  thf('39', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('simplify', [status(thm)], ['38'])).
% 0.76/0.99  thf('40', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_C)))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['19', '39'])).
% 0.76/0.99  thf('41', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('43', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(d4_tmap_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                 ( m1_subset_1 @
% 0.76/0.99                   C @ 
% 0.76/0.99                   ( k1_zfmisc_1 @
% 0.76/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( m1_pre_topc @ D @ A ) =>
% 0.76/0.99                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.76/0.99                     ( k2_partfun1 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.76/0.99                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X4)
% 0.76/0.99          | ~ (v2_pre_topc @ X4)
% 0.76/0.99          | ~ (l1_pre_topc @ X4)
% 0.76/0.99          | ~ (m1_pre_topc @ X5 @ X6)
% 0.76/0.99          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.76/0.99                 (u1_struct_0 @ X5)))
% 0.76/0.99          | ~ (m1_subset_1 @ X7 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.76/0.99          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.76/0.99          | ~ (v1_funct_1 @ X7)
% 0.76/0.99          | ~ (l1_pre_topc @ X6)
% 0.76/0.99          | ~ (v2_pre_topc @ X6)
% 0.76/0.99          | (v2_struct_0 @ X6))),
% 0.76/0.99      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.99  thf('46', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('47', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('48', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['45', '46', '47', '48', '49', '50', '51'])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_C)))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['42', '52'])).
% 0.76/0.99  thf('54', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('55', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_C)))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.99  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('57', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_C))))),
% 0.76/0.99      inference('clc', [status(thm)], ['55', '56'])).
% 0.76/0.99  thf('58', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('59', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99            (u1_struct_0 @ sk_C)))),
% 0.76/0.99      inference('clc', [status(thm)], ['57', '58'])).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F)
% 0.76/0.99            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['40', '41', '59'])).
% 0.76/0.99  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('62', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F)
% 0.76/0.99            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C)))),
% 0.76/0.99      inference('clc', [status(thm)], ['60', '61'])).
% 0.76/0.99  thf('63', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('64', plain,
% 0.76/0.99      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_F)
% 0.76/0.99         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C))),
% 0.76/0.99      inference('clc', [status(thm)], ['62', '63'])).
% 0.76/0.99  thf('65', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('66', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('67', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['13', '18', '64', '65', '66'])).
% 0.76/0.99  thf('68', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C))
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.99  thf('69', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('70', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C)))),
% 0.76/0.99      inference('clc', [status(thm)], ['68', '69'])).
% 0.76/0.99  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('72', plain,
% 0.76/0.99      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99        (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_C))),
% 0.76/0.99      inference('clc', [status(thm)], ['70', '71'])).
% 0.76/0.99  thf('73', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t77_tmap_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.99                   ( ![E:$i]:
% 0.76/0.99                     ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.99                         ( v1_funct_2 @
% 0.76/0.99                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                         ( m1_subset_1 @
% 0.76/0.99                           E @ 
% 0.76/0.99                           ( k1_zfmisc_1 @
% 0.76/0.99                             ( k2_zfmisc_1 @
% 0.76/0.99                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                       ( ![F:$i]:
% 0.76/0.99                         ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.99                             ( v1_funct_2 @
% 0.76/0.99                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                             ( m1_subset_1 @
% 0.76/0.99                               F @ 
% 0.76/0.99                               ( k1_zfmisc_1 @
% 0.76/0.99                                 ( k2_zfmisc_1 @
% 0.76/0.99                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                           ( ( ( r2_funct_2 @
% 0.76/0.99                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.99                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.76/0.99                               ( m1_pre_topc @ D @ C ) ) =>
% 0.76/0.99                             ( r2_funct_2 @
% 0.76/0.99                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.99                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.76/0.99                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('74', plain,
% 0.76/0.99      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X23)
% 0.76/0.99          | ~ (v2_pre_topc @ X23)
% 0.76/0.99          | ~ (l1_pre_topc @ X23)
% 0.76/0.99          | (v2_struct_0 @ X24)
% 0.76/0.99          | ~ (m1_pre_topc @ X24 @ X25)
% 0.76/0.99          | ~ (v1_funct_1 @ X26)
% 0.76/0.99          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23))
% 0.76/0.99          | ~ (m1_subset_1 @ X26 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23))))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23) @ 
% 0.76/0.99             (k3_tmap_1 @ X25 @ X23 @ X27 @ X24 @ X26) @ 
% 0.76/0.99             (k2_tmap_1 @ X25 @ X23 @ X28 @ X24))
% 0.76/0.99          | ~ (r2_funct_2 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23) @ X26 @ 
% 0.76/0.99               (k2_tmap_1 @ X25 @ X23 @ X28 @ X27))
% 0.76/0.99          | ~ (m1_pre_topc @ X24 @ X27)
% 0.76/0.99          | ~ (m1_subset_1 @ X28 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.76/0.99          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.76/0.99          | ~ (v1_funct_1 @ X28)
% 0.76/0.99          | ~ (m1_pre_topc @ X27 @ X25)
% 0.76/0.99          | (v2_struct_0 @ X27)
% 0.76/0.99          | ~ (l1_pre_topc @ X25)
% 0.76/0.99          | ~ (v2_pre_topc @ X25)
% 0.76/0.99          | (v2_struct_0 @ X25))),
% 0.76/0.99      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.76/0.99  thf('75', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ X1)
% 0.76/0.99          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ sk_C)
% 0.76/0.99          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_C))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X2 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ X0)
% 0.76/0.99          | (v2_struct_0 @ X2)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.99  thf('76', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('77', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('80', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ X1)
% 0.76/0.99          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ sk_C)
% 0.76/0.99          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_C))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X2 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ X0)
% 0.76/0.99          | (v2_struct_0 @ X2)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.76/0.99  thf('81', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (m1_subset_1 @ sk_F @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['72', '80'])).
% 0.76/0.99  thf('82', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('83', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('84', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('85', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('86', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('87', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['81', '82', '83', '84', '85', '86'])).
% 0.76/0.99  thf('88', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('simplify', [status(thm)], ['87'])).
% 0.76/0.99  thf('89', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['3', '88'])).
% 0.76/0.99  thf('90', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('91', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['89', '90'])).
% 0.76/0.99  thf('92', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99           (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99        | (v2_struct_0 @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '91'])).
% 0.76/0.99  thf('93', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('94', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('simplify', [status(thm)], ['38'])).
% 0.76/0.99  thf('95', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_D)))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['93', '94'])).
% 0.76/0.99  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('97', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_D))))),
% 0.76/0.99      inference('clc', [status(thm)], ['95', '96'])).
% 0.76/0.99  thf('98', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('99', plain,
% 0.76/0.99      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99            (u1_struct_0 @ sk_D)))),
% 0.76/0.99      inference('clc', [status(thm)], ['97', '98'])).
% 0.76/0.99  thf('100', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('101', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['45', '46', '47', '48', '49', '50', '51'])).
% 0.76/0.99  thf('102', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_D)))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['100', '101'])).
% 0.76/0.99  thf('103', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('104', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_D))))),
% 0.76/0.99      inference('clc', [status(thm)], ['102', '103'])).
% 0.76/0.99  thf('105', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('106', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99            (u1_struct_0 @ sk_D)))),
% 0.76/0.99      inference('clc', [status(thm)], ['104', '105'])).
% 0.76/0.99  thf('107', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('108', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99        | (v2_struct_0 @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['92', '107'])).
% 0.76/0.99  thf('109', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('110', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('111', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(dt_k3_tmap_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.76/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.99         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.76/0.99         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.76/0.99         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.76/0.99         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99         ( m1_subset_1 @
% 0.76/0.99           E @ 
% 0.76/0.99           ( k1_zfmisc_1 @
% 0.76/0.99             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.76/0.99         ( v1_funct_2 @
% 0.76/0.99           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.76/0.99           ( u1_struct_0 @ B ) ) & 
% 0.76/0.99         ( m1_subset_1 @
% 0.76/0.99           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.76/0.99           ( k1_zfmisc_1 @
% 0.76/0.99             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.76/0.99  thf('112', plain,
% 0.76/0.99      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X13 @ X14)
% 0.76/0.99          | ~ (m1_pre_topc @ X15 @ X14)
% 0.76/0.99          | ~ (l1_pre_topc @ X16)
% 0.76/0.99          | ~ (v2_pre_topc @ X16)
% 0.76/0.99          | (v2_struct_0 @ X16)
% 0.76/0.99          | ~ (l1_pre_topc @ X14)
% 0.76/0.99          | ~ (v2_pre_topc @ X14)
% 0.76/0.99          | (v2_struct_0 @ X14)
% 0.76/0.99          | ~ (v1_funct_1 @ X17)
% 0.76/0.99          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.76/0.99          | ~ (m1_subset_1 @ X17 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.76/0.99          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.76/0.99             (k1_zfmisc_1 @ 
% 0.76/0.99              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.76/0.99  thf('113', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99           (k1_zfmisc_1 @ 
% 0.76/0.99            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | (v2_struct_0 @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['111', '112'])).
% 0.76/0.99  thf('114', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('115', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('116', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('118', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99           (k1_zfmisc_1 @ 
% 0.76/0.99            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | (v2_struct_0 @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.99      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.76/0.99  thf('119', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k1_zfmisc_1 @ 
% 0.76/0.99              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['110', '118'])).
% 0.76/0.99  thf('120', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('121', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('122', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('123', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (k1_zfmisc_1 @ 
% 0.76/0.99              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.76/0.99      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.76/0.99  thf('124', plain,
% 0.76/0.99      (((m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99         (k1_zfmisc_1 @ 
% 0.76/0.99          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['109', '123'])).
% 0.76/0.99  thf('125', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('126', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99           (k1_zfmisc_1 @ 
% 0.76/0.99            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.76/0.99      inference('clc', [status(thm)], ['124', '125'])).
% 0.76/0.99  thf('127', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('128', plain,
% 0.76/0.99      ((m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('clc', [status(thm)], ['126', '127'])).
% 0.76/0.99  thf('129', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('130', plain,
% 0.76/0.99      ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('demod', [status(thm)], ['128', '129'])).
% 0.76/0.99  thf('131', plain,
% 0.76/0.99      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X23)
% 0.76/0.99          | ~ (v2_pre_topc @ X23)
% 0.76/0.99          | ~ (l1_pre_topc @ X23)
% 0.76/0.99          | (v2_struct_0 @ X24)
% 0.76/0.99          | ~ (m1_pre_topc @ X24 @ X25)
% 0.76/0.99          | ~ (v1_funct_1 @ X26)
% 0.76/0.99          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23))
% 0.76/0.99          | ~ (m1_subset_1 @ X26 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23))))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23) @ 
% 0.76/0.99             (k3_tmap_1 @ X25 @ X23 @ X27 @ X24 @ X26) @ 
% 0.76/0.99             (k2_tmap_1 @ X25 @ X23 @ X28 @ X24))
% 0.76/0.99          | ~ (r2_funct_2 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X23) @ X26 @ 
% 0.76/0.99               (k2_tmap_1 @ X25 @ X23 @ X28 @ X27))
% 0.76/0.99          | ~ (m1_pre_topc @ X24 @ X27)
% 0.76/0.99          | ~ (m1_subset_1 @ X28 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.76/0.99          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.76/0.99          | ~ (v1_funct_1 @ X28)
% 0.76/0.99          | ~ (m1_pre_topc @ X27 @ X25)
% 0.76/0.99          | (v2_struct_0 @ X27)
% 0.76/0.99          | ~ (l1_pre_topc @ X25)
% 0.76/0.99          | ~ (v2_pre_topc @ X25)
% 0.76/0.99          | (v2_struct_0 @ X25))),
% 0.76/0.99      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.76/0.99  thf('132', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ X1)
% 0.76/0.99          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.76/0.99          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.76/0.99          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ X0)
% 0.76/0.99          | (v2_struct_0 @ X2)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['130', '131'])).
% 0.76/0.99  thf('133', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('134', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('135', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('136', plain,
% 0.76/0.99      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X13 @ X14)
% 0.76/0.99          | ~ (m1_pre_topc @ X15 @ X14)
% 0.76/0.99          | ~ (l1_pre_topc @ X16)
% 0.76/0.99          | ~ (v2_pre_topc @ X16)
% 0.76/0.99          | (v2_struct_0 @ X16)
% 0.76/0.99          | ~ (l1_pre_topc @ X14)
% 0.76/0.99          | ~ (v2_pre_topc @ X14)
% 0.76/0.99          | (v2_struct_0 @ X14)
% 0.76/0.99          | ~ (v1_funct_1 @ X17)
% 0.76/0.99          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.76/0.99          | ~ (m1_subset_1 @ X17 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.76/0.99          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.76/0.99             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.76/0.99  thf('137', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | (v2_struct_0 @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['135', '136'])).
% 0.76/0.99  thf('138', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('139', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('140', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('141', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('142', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | (v2_struct_0 @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.99      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.76/0.99  thf('143', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['134', '142'])).
% 0.76/0.99  thf('144', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('145', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('146', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('147', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.76/0.99             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.99      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.76/0.99  thf('148', plain,
% 0.76/0.99      (((v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['133', '147'])).
% 0.76/0.99  thf('149', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('150', plain,
% 0.76/0.99      (((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['148', '149'])).
% 0.76/0.99  thf('151', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('152', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.99      inference('clc', [status(thm)], ['150', '151'])).
% 0.76/0.99  thf('153', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('154', plain,
% 0.76/0.99      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('clc', [status(thm)], ['152', '153'])).
% 0.76/0.99  thf('155', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('156', plain,
% 0.76/0.99      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.76/0.99      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.76/0.99  thf('157', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('158', plain,
% 0.76/0.99      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X13 @ X14)
% 0.76/0.99          | ~ (m1_pre_topc @ X15 @ X14)
% 0.76/0.99          | ~ (l1_pre_topc @ X16)
% 0.76/0.99          | ~ (v2_pre_topc @ X16)
% 0.76/0.99          | (v2_struct_0 @ X16)
% 0.76/0.99          | ~ (l1_pre_topc @ X14)
% 0.76/0.99          | ~ (v2_pre_topc @ X14)
% 0.76/0.99          | (v2_struct_0 @ X14)
% 0.76/0.99          | ~ (v1_funct_1 @ X17)
% 0.76/0.99          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.76/0.99          | ~ (m1_subset_1 @ X17 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.76/0.99          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.76/0.99  thf('159', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | (v2_struct_0 @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['157', '158'])).
% 0.76/0.99  thf('160', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('161', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('162', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('163', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('164', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F))
% 0.76/0.99          | (v2_struct_0 @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.99      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 0.76/0.99  thf('165', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['156', '164'])).
% 0.76/0.99  thf('166', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('167', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('168', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('169', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ sk_F)))),
% 0.76/0.99      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 0.76/0.99  thf('170', plain,
% 0.76/0.99      (((v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['155', '169'])).
% 0.76/0.99  thf('171', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('172', plain,
% 0.76/0.99      (((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['170', '171'])).
% 0.76/0.99  thf('173', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('174', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.76/0.99      inference('clc', [status(thm)], ['172', '173'])).
% 0.76/0.99  thf('175', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('176', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.76/0.99      inference('clc', [status(thm)], ['174', '175'])).
% 0.76/0.99  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('178', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('179', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ X1)
% 0.76/0.99          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.76/0.99          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.76/0.99          | ~ (m1_pre_topc @ X2 @ X0)
% 0.76/0.99          | (v2_struct_0 @ X2)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['132', '154', '176', '177', '178'])).
% 0.76/0.99  thf('180', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | ~ (m1_subset_1 @ sk_F @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.76/0.99          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['108', '179'])).
% 0.76/0.99  thf('181', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_F @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('182', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('183', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('184', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('185', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('186', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('187', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['180', '181', '182', '183', '184', '185', '186'])).
% 0.76/0.99  thf('188', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('simplify', [status(thm)], ['187'])).
% 0.76/0.99  thf('189', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (v2_struct_0 @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_E)
% 0.76/0.99        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['1', '188'])).
% 0.76/0.99  thf('190', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('191', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t7_tsep_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( m1_pre_topc @ B @ A ) =>
% 0.76/0.99           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.76/0.99  thf('192', plain,
% 0.76/0.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X29 @ X30)
% 0.76/0.99          | (m1_pre_topc @ X31 @ X30)
% 0.76/0.99          | ~ (m1_pre_topc @ X31 @ X29)
% 0.76/0.99          | ~ (l1_pre_topc @ X30)
% 0.76/0.99          | ~ (v2_pre_topc @ X30))),
% 0.76/0.99      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.76/0.99  thf('193', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | (m1_pre_topc @ X0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['191', '192'])).
% 0.76/0.99  thf('194', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('195', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('196', plain,
% 0.76/0.99      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['193', '194', '195'])).
% 0.76/0.99  thf('197', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.76/0.99      inference('sup-', [status(thm)], ['190', '196'])).
% 0.76/0.99  thf('198', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.76/0.99      inference('sup-', [status(thm)], ['190', '196'])).
% 0.76/0.99  thf('199', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('200', plain,
% 0.76/0.99      ((m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('clc', [status(thm)], ['126', '127'])).
% 0.76/0.99  thf('201', plain,
% 0.76/0.99      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X8)
% 0.76/0.99          | ~ (v2_pre_topc @ X8)
% 0.76/0.99          | ~ (l1_pre_topc @ X8)
% 0.76/0.99          | ~ (m1_pre_topc @ X9 @ X10)
% 0.76/0.99          | ~ (m1_pre_topc @ X9 @ X11)
% 0.76/0.99          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.76/0.99                 X12 @ (u1_struct_0 @ X9)))
% 0.76/0.99          | ~ (m1_subset_1 @ X12 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.76/0.99          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.76/0.99          | ~ (v1_funct_1 @ X12)
% 0.76/0.99          | ~ (m1_pre_topc @ X11 @ X10)
% 0.76/0.99          | ~ (l1_pre_topc @ X10)
% 0.76/0.99          | ~ (v2_pre_topc @ X10)
% 0.76/0.99          | (v2_struct_0 @ X10))),
% 0.76/0.99      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.76/0.99  thf('202', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.76/0.99              (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99                 (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['200', '201'])).
% 0.76/0.99  thf('203', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('204', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('205', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.99          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.76/0.99              (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99                 (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['202', '203', '204'])).
% 0.76/0.99  thf('206', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('207', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.76/0.99      inference('clc', [status(thm)], ['174', '175'])).
% 0.76/0.99  thf('208', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('209', plain,
% 0.76/0.99      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('clc', [status(thm)], ['152', '153'])).
% 0.76/0.99  thf('210', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('211', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('212', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['205', '206', '207', '208', '209', '210', '211'])).
% 0.76/0.99  thf('213', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (l1_pre_topc @ sk_C)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['199', '212'])).
% 0.76/0.99  thf('214', plain, ((l1_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('215', plain, ((v2_pre_topc @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.76/0.99  thf('216', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.76/0.99          | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['213', '214', '215'])).
% 0.76/0.99  thf('217', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.76/0.99        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['198', '216'])).
% 0.76/0.99  thf('218', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('219', plain,
% 0.76/0.99      ((m1_subset_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('clc', [status(thm)], ['126', '127'])).
% 0.76/0.99  thf('220', plain,
% 0.76/0.99      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X4)
% 0.76/0.99          | ~ (v2_pre_topc @ X4)
% 0.76/0.99          | ~ (l1_pre_topc @ X4)
% 0.76/0.99          | ~ (m1_pre_topc @ X5 @ X6)
% 0.76/0.99          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.76/0.99                 (u1_struct_0 @ X5)))
% 0.76/0.99          | ~ (m1_subset_1 @ X7 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.76/0.99          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.76/0.99          | ~ (v1_funct_1 @ X7)
% 0.76/0.99          | ~ (l1_pre_topc @ X6)
% 0.76/0.99          | ~ (v2_pre_topc @ X6)
% 0.76/0.99          | (v2_struct_0 @ X6))),
% 0.76/0.99      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.76/0.99  thf('221', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_D)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_D)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_D)
% 0.76/0.99          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99              (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99                 (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['219', '220'])).
% 0.76/0.99  thf('222', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('223', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X0 @ X1)
% 0.76/0.99          | (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X1)
% 0.76/0.99          | ~ (v2_pre_topc @ X1))),
% 0.76/0.99      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.76/0.99  thf('224', plain,
% 0.76/0.99      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.76/0.99      inference('sup-', [status(thm)], ['222', '223'])).
% 0.76/0.99  thf('225', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('226', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('227', plain, ((v2_pre_topc @ sk_D)),
% 0.76/0.99      inference('demod', [status(thm)], ['224', '225', '226'])).
% 0.76/0.99  thf('228', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('229', plain,
% 0.76/0.99      (![X2 : $i, X3 : $i]:
% 0.76/0.99         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.76/0.99  thf('230', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.76/0.99      inference('sup-', [status(thm)], ['228', '229'])).
% 0.76/0.99  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('232', plain, ((l1_pre_topc @ sk_D)),
% 0.76/0.99      inference('demod', [status(thm)], ['230', '231'])).
% 0.76/0.99  thf('233', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('234', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('235', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_D)
% 0.76/0.99          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.76/0.99          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99              (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.76/0.99                 (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['221', '227', '232', '233', '234'])).
% 0.76/0.99  thf('236', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('237', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.76/0.99      inference('clc', [status(thm)], ['174', '175'])).
% 0.76/0.99  thf('238', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('239', plain,
% 0.76/0.99      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('clc', [status(thm)], ['152', '153'])).
% 0.76/0.99  thf('240', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('241', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.76/0.99      inference('sup+', [status(thm)], ['99', '106'])).
% 0.76/0.99  thf('242', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_D)
% 0.76/0.99          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['235', '236', '237', '238', '239', '240', '241'])).
% 0.76/0.99  thf('243', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.76/0.99        | (v2_struct_0 @ sk_D))),
% 0.76/0.99      inference('sup-', [status(thm)], ['218', '242'])).
% 0.76/0.99  thf('244', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('245', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_D)
% 0.76/0.99        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E))))),
% 0.76/0.99      inference('clc', [status(thm)], ['243', '244'])).
% 0.76/0.99  thf('246', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('247', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99         sk_E)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.76/0.99      inference('clc', [status(thm)], ['245', '246'])).
% 0.76/0.99  thf('248', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('249', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['217', '247', '248'])).
% 0.76/0.99  thf('250', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('251', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.76/0.99      inference('clc', [status(thm)], ['249', '250'])).
% 0.76/0.99  thf('252', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('253', plain,
% 0.76/0.99      (((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.76/0.99      inference('clc', [status(thm)], ['251', '252'])).
% 0.76/0.99  thf('254', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | (v2_struct_0 @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_E)
% 0.76/0.99        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E) @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.76/0.99      inference('demod', [status(thm)], ['189', '197', '253'])).
% 0.76/0.99  thf('255', plain,
% 0.76/0.99      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)) @ 
% 0.76/0.99          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('256', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('257', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('258', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.76/0.99  thf('259', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.99          | (v2_struct_0 @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['257', '258'])).
% 0.76/0.99  thf('260', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('261', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('262', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | (v2_struct_0 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['259', '260', '261'])).
% 0.76/0.99  thf('263', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_A)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_D)))
% 0.76/0.99        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['256', '262'])).
% 0.76/0.99  thf('264', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99            (u1_struct_0 @ sk_D)))),
% 0.76/0.99      inference('clc', [status(thm)], ['104', '105'])).
% 0.76/0.99  thf('265', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('266', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_A)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['263', '264', '265'])).
% 0.76/0.99  thf('267', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('268', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.76/0.99      inference('clc', [status(thm)], ['266', '267'])).
% 0.76/0.99  thf('269', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('270', plain,
% 0.76/0.99      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.76/0.99         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.76/0.99      inference('clc', [status(thm)], ['268', '269'])).
% 0.76/0.99  thf('271', plain,
% 0.76/0.99      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.76/0.99      inference('demod', [status(thm)], ['255', '270'])).
% 0.76/0.99  thf('272', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('273', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | (v2_struct_0 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['259', '260', '261'])).
% 0.76/0.99  thf('274', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_A)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_E)))
% 0.76/0.99        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['272', '273'])).
% 0.76/0.99  thf('275', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.76/0.99      inference('sup-', [status(thm)], ['190', '196'])).
% 0.76/0.99  thf('276', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_C)
% 0.76/0.99          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 sk_F @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['45', '46', '47', '48', '49', '50', '51'])).
% 0.76/0.99  thf('277', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_E)))
% 0.76/0.99        | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['275', '276'])).
% 0.76/0.99  thf('278', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('279', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_C)
% 0.76/0.99        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_F @ (u1_struct_0 @ sk_E))))),
% 0.76/0.99      inference('clc', [status(thm)], ['277', '278'])).
% 0.76/0.99  thf('280', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('281', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.76/0.99            (u1_struct_0 @ sk_E)))),
% 0.76/0.99      inference('clc', [status(thm)], ['279', '280'])).
% 0.76/0.99  thf('282', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.76/0.99      inference('sup-', [status(thm)], ['190', '196'])).
% 0.76/0.99  thf('283', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_A)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.76/0.99            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['274', '281', '282'])).
% 0.76/0.99  thf('284', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('285', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.76/0.99            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.76/0.99      inference('clc', [status(thm)], ['283', '284'])).
% 0.76/0.99  thf('286', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('287', plain,
% 0.76/0.99      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.76/0.99         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.76/0.99      inference('clc', [status(thm)], ['285', '286'])).
% 0.76/0.99  thf('288', plain,
% 0.76/0.99      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.76/0.99          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.76/0.99      inference('demod', [status(thm)], ['271', '287'])).
% 0.76/0.99  thf('289', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('290', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('291', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X0)
% 0.76/0.99          | ~ (v2_pre_topc @ X0)
% 0.76/0.99          | ~ (l1_pre_topc @ X0)
% 0.76/0.99          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.99          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.76/0.99          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.99          | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)],
% 0.76/0.99                ['205', '206', '207', '208', '209', '210', '211'])).
% 0.76/0.99  thf('292', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.76/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.99          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.99          | (v2_struct_0 @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['290', '291'])).
% 0.76/0.99  thf('293', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('294', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('295', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((v2_struct_0 @ sk_B)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.99          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.76/0.99          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.76/0.99              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.76/0.99          | (v2_struct_0 @ sk_A))),
% 0.76/0.99      inference('demod', [status(thm)], ['292', '293', '294'])).
% 0.76/0.99  thf('296', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_A)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.76/0.99        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['289', '295'])).
% 0.76/0.99  thf('297', plain,
% 0.76/0.99      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99         sk_E)
% 0.76/0.99         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.76/0.99      inference('clc', [status(thm)], ['245', '246'])).
% 0.76/0.99  thf('298', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('299', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_A)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['296', '297', '298'])).
% 0.76/0.99  thf('300', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('301', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_B)
% 0.76/0.99        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.76/0.99      inference('clc', [status(thm)], ['299', '300'])).
% 0.76/0.99  thf('302', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('303', plain,
% 0.76/0.99      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.76/0.99         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.76/0.99         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.76/0.99            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.76/0.99      inference('clc', [status(thm)], ['301', '302'])).
% 0.76/0.99  thf('304', plain,
% 0.76/0.99      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99          (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.76/0.99           sk_E) @ 
% 0.76/0.99          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.76/0.99      inference('demod', [status(thm)], ['288', '303'])).
% 0.76/0.99  thf('305', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_E)
% 0.76/0.99        | (v2_struct_0 @ sk_C)
% 0.76/0.99        | (v2_struct_0 @ sk_D)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['254', '304'])).
% 0.76/0.99  thf('306', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('307', plain,
% 0.76/0.99      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_E))),
% 0.76/0.99      inference('sup-', [status(thm)], ['305', '306'])).
% 0.76/0.99  thf('308', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('309', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_C))),
% 0.76/0.99      inference('clc', [status(thm)], ['307', '308'])).
% 0.76/0.99  thf('310', plain, (~ (v2_struct_0 @ sk_E)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('311', plain, ((v2_struct_0 @ sk_C)),
% 0.76/0.99      inference('clc', [status(thm)], ['309', '310'])).
% 0.76/0.99  thf('312', plain, ($false), inference('demod', [status(thm)], ['0', '311'])).
% 0.76/0.99  
% 0.76/0.99  % SZS output end Refutation
% 0.76/0.99  
% 0.76/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
