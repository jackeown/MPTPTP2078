%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H9dDSaY6Pl

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 649 expanded)
%              Number of leaves         :   28 ( 201 expanded)
%              Depth                    :   20
%              Number of atoms          : 1719 (28345 expanded)
%              Number of equality atoms :   20 (  68 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v5_pre_topc @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X19 @ X20 @ X18 @ X21 ) @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('7',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','10','15','16','17','18','19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( ( k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) @ X13 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( k2_tmap_1 @ X7 @ X5 @ X8 @ X6 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X8 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('45',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['24','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('67',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','68','71','72','73'])).

thf('75',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('85',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['66','67'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['23'])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('100',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['66','67'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('106',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('110',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('114',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('116',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['86','100','114','115'])).

thf('117',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H9dDSaY6Pl
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 71 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(t89_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                         ( v1_funct_2 @
% 0.20/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                         ( v5_pre_topc @ E @ C @ B ) & 
% 0.20/0.49                         ( m1_subset_1 @
% 0.20/0.49                           E @ 
% 0.20/0.49                           ( k1_zfmisc_1 @
% 0.20/0.49                             ( k2_zfmisc_1 @
% 0.20/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.49                         ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.49                           ( v1_funct_2 @
% 0.20/0.49                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                           ( v5_pre_topc @
% 0.20/0.49                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B ) & 
% 0.20/0.49                           ( m1_subset_1 @
% 0.20/0.49                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                             ( k1_zfmisc_1 @
% 0.20/0.49                               ( k2_zfmisc_1 @
% 0.20/0.49                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49                ( l1_pre_topc @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                      ( ![E:$i]:
% 0.20/0.49                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                            ( v1_funct_2 @
% 0.20/0.49                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                            ( v5_pre_topc @ E @ C @ B ) & 
% 0.20/0.49                            ( m1_subset_1 @
% 0.20/0.49                              E @ 
% 0.20/0.49                              ( k1_zfmisc_1 @
% 0.20/0.49                                ( k2_zfmisc_1 @
% 0.20/0.49                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                          ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.49                            ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.49                              ( v1_funct_2 @
% 0.20/0.49                                ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                                ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                              ( v5_pre_topc @
% 0.20/0.49                                ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B ) & 
% 0.20/0.49                              ( m1_subset_1 @
% 0.20/0.49                                ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.49                                ( k1_zfmisc_1 @
% 0.20/0.49                                  ( k2_zfmisc_1 @
% 0.20/0.49                                    ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t89_tmap_1])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(fc2_tmap_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.20/0.49         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49         ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @
% 0.20/0.49           C @ 
% 0.20/0.49           ( k1_zfmisc_1 @
% 0.20/0.49             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.20/0.49         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.49         ( v1_funct_2 @
% 0.20/0.49           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.20/0.49           ( u1_struct_0 @ B ) ) & 
% 0.20/0.49         ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X18 @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.20/0.49          | ~ (v5_pre_topc @ X18 @ X19 @ X20)
% 0.20/0.49          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.20/0.49          | ~ (v1_funct_1 @ X18)
% 0.20/0.49          | ~ (l1_pre_topc @ X20)
% 0.20/0.49          | ~ (v2_pre_topc @ X20)
% 0.20/0.49          | (v2_struct_0 @ X20)
% 0.20/0.49          | ~ (l1_pre_topc @ X19)
% 0.20/0.49          | ~ (v2_pre_topc @ X19)
% 0.20/0.49          | (v2_struct_0 @ X19)
% 0.20/0.49          | (v2_struct_0 @ X21)
% 0.20/0.49          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.49          | (v5_pre_topc @ (k2_tmap_1 @ X19 @ X20 @ X18 @ X21) @ X21 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ X0 @ sk_B)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_C)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.49          | (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X1)
% 0.20/0.49          | ~ (v2_pre_topc @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_m1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ X0 @ sk_B)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_C)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['4', '10', '15', '16', '17', '18', '19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_D)
% 0.20/0.49        | (v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.20/0.49        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49             sk_D @ sk_B)
% 0.20/0.49        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49           sk_D @ sk_B))
% 0.20/0.49         <= (~
% 0.20/0.49             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               sk_D @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['23'])).
% 0.20/0.49  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d5_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                         ( v1_funct_2 @
% 0.20/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                         ( m1_subset_1 @
% 0.20/0.49                           E @ 
% 0.20/0.49                           ( k1_zfmisc_1 @
% 0.20/0.49                             ( k2_zfmisc_1 @
% 0.20/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.49                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.49                           ( k2_partfun1 @
% 0.20/0.49                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.49                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X9)
% 0.20/0.49          | ~ (v2_pre_topc @ X9)
% 0.20/0.49          | ~ (l1_pre_topc @ X9)
% 0.20/0.49          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.49          | ~ (m1_pre_topc @ X10 @ X12)
% 0.20/0.49          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 0.20/0.49                 X13 @ (u1_struct_0 @ X10)))
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 0.20/0.49          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (m1_pre_topc @ X12 @ X11)
% 0.20/0.49          | ~ (l1_pre_topc @ X11)
% 0.20/0.49          | ~ (v2_pre_topc @ X11)
% 0.20/0.49          | (v2_struct_0 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.49          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.49          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '34'])).
% 0.20/0.49  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.49          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49               sk_E @ (u1_struct_0 @ sk_D)))
% 0.20/0.49        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '38'])).
% 0.20/0.49  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d4_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                 ( m1_subset_1 @
% 0.20/0.49                   C @ 
% 0.20/0.49                   ( k1_zfmisc_1 @
% 0.20/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.49                     ( k2_partfun1 @
% 0.20/0.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X5)
% 0.20/0.49          | ~ (v2_pre_topc @ X5)
% 0.20/0.49          | ~ (l1_pre_topc @ X5)
% 0.20/0.49          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.49          | ((k2_tmap_1 @ X7 @ X5 @ X8 @ X6)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X8 @ 
% 0.20/0.49                 (u1_struct_0 @ X6)))
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.20/0.49          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (v1_funct_1 @ X8)
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_C)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_C)
% 0.20/0.49          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.20/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.20/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49               sk_E @ (u1_struct_0 @ sk_D)))
% 0.20/0.49        | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '50'])).
% 0.20/0.49  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_C)
% 0.20/0.49        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.20/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.20/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.20/0.49         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.49            (u1_struct_0 @ sk_D)))),
% 0.20/0.49      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '55', '56'])).
% 0.20/0.49  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)))),
% 0.20/0.49      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ sk_D @ sk_B))
% 0.20/0.49         <= (~
% 0.20/0.49             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               sk_D @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k2_tmap_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49         ( m1_subset_1 @
% 0.20/0.49           C @ 
% 0.20/0.49           ( k1_zfmisc_1 @
% 0.20/0.49             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.20/0.49         ( l1_struct_0 @ D ) ) =>
% 0.20/0.49       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.49         ( v1_funct_2 @
% 0.20/0.49           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.20/0.49           ( u1_struct_0 @ B ) ) & 
% 0.20/0.49         ( m1_subset_1 @
% 0.20/0.49           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.20/0.49           ( k1_zfmisc_1 @
% 0.20/0.49             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X14 @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.20/0.49          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.20/0.49          | ~ (v1_funct_1 @ X14)
% 0.20/0.49          | ~ (l1_struct_0 @ X16)
% 0.20/0.49          | ~ (l1_struct_0 @ X15)
% 0.20/0.49          | ~ (l1_struct_0 @ X17)
% 0.20/0.49          | (v1_funct_2 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.20/0.49             (u1_struct_0 @ X17) @ (u1_struct_0 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 0.20/0.49           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('67', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('68', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('70', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 0.20/0.49           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (l1_struct_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['65', '68', '71', '72', '73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['23'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.20/0.49           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      ((~ (l1_struct_0 @ sk_D))
% 0.20/0.49         <= (~
% 0.20/0.49             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['74', '77'])).
% 0.20/0.49  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('81', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.49  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('83', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.49  thf('84', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('85', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.49      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['78', '85'])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X14 @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.20/0.49          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.20/0.49          | ~ (v1_funct_1 @ X14)
% 0.20/0.49          | ~ (l1_struct_0 @ X16)
% 0.20/0.49          | ~ (l1_struct_0 @ X15)
% 0.20/0.49          | ~ (l1_struct_0 @ X17)
% 0.20/0.49          | (v1_funct_1 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.20/0.49  thf('89', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0))
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.49  thf('90', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0))
% 0.20/0.49          | ~ (l1_struct_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.20/0.49  thf('95', plain,
% 0.20/0.49      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))
% 0.20/0.49         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.20/0.49      inference('split', [status(esa)], ['23'])).
% 0.20/0.49  thf('97', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)))
% 0.20/0.49         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      ((~ (l1_struct_0 @ sk_D))
% 0.20/0.49         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['94', '97'])).
% 0.20/0.49  thf('99', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.49      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.49      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('102', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X14 @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.20/0.49          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.20/0.49          | ~ (v1_funct_1 @ X14)
% 0.20/0.49          | ~ (l1_struct_0 @ X16)
% 0.20/0.49          | ~ (l1_struct_0 @ X15)
% 0.20/0.49          | ~ (l1_struct_0 @ X17)
% 0.20/0.49          | (m1_subset_1 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16)))))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.20/0.49  thf('103', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ 
% 0.20/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.49  thf('104', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('107', plain,
% 0.20/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('108', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ 
% 0.20/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.49          | ~ (l1_struct_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.20/0.49  thf('109', plain,
% 0.20/0.49      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.49         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('110', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49           (k1_zfmisc_1 @ 
% 0.20/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.49      inference('split', [status(esa)], ['23'])).
% 0.20/0.49  thf('111', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.20/0.49           (k1_zfmisc_1 @ 
% 0.20/0.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.49  thf('112', plain,
% 0.20/0.49      ((~ (l1_struct_0 @ sk_D))
% 0.20/0.49         <= (~
% 0.20/0.49             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49               (k1_zfmisc_1 @ 
% 0.20/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['108', '111'])).
% 0.20/0.49  thf('113', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.49      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.49  thf('114', plain,
% 0.20/0.49      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49         (k1_zfmisc_1 @ 
% 0.20/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.20/0.49      inference('demod', [status(thm)], ['112', '113'])).
% 0.20/0.49  thf('115', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_D @ 
% 0.20/0.49         sk_B)) | 
% 0.20/0.49       ~
% 0.20/0.49       ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49         (k1_zfmisc_1 @ 
% 0.20/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.20/0.49       ~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.49         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['23'])).
% 0.20/0.49  thf('116', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_D @ 
% 0.20/0.49         sk_B))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['86', '100', '114', '115'])).
% 0.20/0.49  thf('117', plain,
% 0.20/0.49      (~ (v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ sk_D @ sk_B)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['62', '116'])).
% 0.20/0.49  thf('118', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '117'])).
% 0.20/0.49  thf('119', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('120', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['118', '119'])).
% 0.20/0.49  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('122', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.49      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.49  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
