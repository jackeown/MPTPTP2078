%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SXz3Y8W7Ze

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:07 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 723 expanded)
%              Number of leaves         :   26 ( 222 expanded)
%              Depth                    :   32
%              Number of atoms          : 3062 (26699 expanded)
%              Number of equality atoms :   31 (  91 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(t78_tmap_1,conjecture,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X16 @ ( k3_tmap_1 @ X18 @ X15 @ X17 @ X17 @ X16 ) )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
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
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('16',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X7 )
      | ( ( k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) @ X8 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','42'])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','55','56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('65',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ ( k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X22 ) @ ( k2_tmap_1 @ X21 @ X19 @ X24 @ X20 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) @ X22 @ ( k2_tmap_1 @ X21 @ X19 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','42'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('103',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X10 @ X12 @ X11 @ X9 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X12 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ ( k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X22 ) @ ( k2_tmap_1 @ X21 @ X19 @ X24 @ X20 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) @ X22 @ ( k2_tmap_1 @ X21 @ X19 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('123',plain,(
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
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('126',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X10 @ X12 @ X11 @ X9 @ X13 ) @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['125','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['124','138'])).

thf('140',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('141',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('148',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X10 @ X12 @ X11 @ X9 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['147','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['146','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('167',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
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
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','145','167','168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172','173','174','175','176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','179'])).

thf('181',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    $false ),
    inference(demod,[status(thm)],['0','190'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SXz3Y8W7Ze
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 408 iterations in 0.344s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.79  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.60/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.79  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.60/0.79  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.60/0.79  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.79  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.60/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.79  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.60/0.79  thf(t78_tmap_1, conjecture,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.79             ( l1_pre_topc @ B ) ) =>
% 0.60/0.79           ( ![C:$i]:
% 0.60/0.79             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.79               ( ![D:$i]:
% 0.60/0.79                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.79                   ( ![E:$i]:
% 0.60/0.79                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.79                         ( v1_funct_2 @
% 0.60/0.79                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                         ( m1_subset_1 @
% 0.60/0.79                           E @ 
% 0.60/0.79                           ( k1_zfmisc_1 @
% 0.60/0.79                             ( k2_zfmisc_1 @
% 0.60/0.79                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79                       ( ( m1_pre_topc @ C @ D ) =>
% 0.60/0.79                         ( r2_funct_2 @
% 0.60/0.79                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.60/0.79                           ( k3_tmap_1 @
% 0.60/0.79                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.60/0.79                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i]:
% 0.60/0.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.79            ( l1_pre_topc @ A ) ) =>
% 0.60/0.79          ( ![B:$i]:
% 0.60/0.79            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.79                ( l1_pre_topc @ B ) ) =>
% 0.60/0.79              ( ![C:$i]:
% 0.60/0.79                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.79                  ( ![D:$i]:
% 0.60/0.79                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.79                      ( ![E:$i]:
% 0.60/0.79                        ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.79                            ( v1_funct_2 @
% 0.60/0.79                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                            ( m1_subset_1 @
% 0.60/0.79                              E @ 
% 0.60/0.79                              ( k1_zfmisc_1 @
% 0.60/0.79                                ( k2_zfmisc_1 @
% 0.60/0.79                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79                          ( ( m1_pre_topc @ C @ D ) =>
% 0.60/0.79                            ( r2_funct_2 @
% 0.60/0.79                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.60/0.79                              ( k3_tmap_1 @
% 0.60/0.79                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.60/0.79                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 0.60/0.79  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t2_tsep_1, axiom,
% 0.60/0.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.60/0.79  thf('3', plain,
% 0.60/0.79      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.79      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.79  thf('4', plain,
% 0.60/0.79      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.79      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.79  thf('5', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_E @ 
% 0.60/0.79        (k1_zfmisc_1 @ 
% 0.60/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t74_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.79             ( l1_pre_topc @ B ) ) =>
% 0.60/0.79           ( ![C:$i]:
% 0.60/0.79             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.79               ( ![D:$i]:
% 0.60/0.79                 ( ( ( v1_funct_1 @ D ) & 
% 0.60/0.79                     ( v1_funct_2 @
% 0.60/0.79                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                     ( m1_subset_1 @
% 0.60/0.79                       D @ 
% 0.60/0.79                       ( k1_zfmisc_1 @
% 0.60/0.79                         ( k2_zfmisc_1 @
% 0.60/0.79                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79                   ( r2_funct_2 @
% 0.60/0.79                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.60/0.79                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X15)
% 0.60/0.79          | ~ (v2_pre_topc @ X15)
% 0.60/0.79          | ~ (l1_pre_topc @ X15)
% 0.60/0.79          | ~ (v1_funct_1 @ X16)
% 0.60/0.79          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 0.60/0.79          | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ X16 @ 
% 0.60/0.79             (k3_tmap_1 @ X18 @ X15 @ X17 @ X17 @ X16))
% 0.60/0.79          | ~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.79          | (v2_struct_0 @ X17)
% 0.60/0.79          | ~ (l1_pre_topc @ X18)
% 0.60/0.79          | ~ (v2_pre_topc @ X18)
% 0.60/0.79          | (v2_struct_0 @ X18))),
% 0.60/0.79      inference('cnf', [status(esa)], [t74_tmap_1])).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E))
% 0.60/0.79          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.79          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('11', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('12', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E))
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_B)
% 0.60/0.79        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E))
% 0.60/0.79        | (v2_struct_0 @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['4', '12'])).
% 0.60/0.79  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.79      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.79      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_E @ 
% 0.60/0.79        (k1_zfmisc_1 @ 
% 0.60/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(d5_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.79             ( l1_pre_topc @ B ) ) =>
% 0.60/0.79           ( ![C:$i]:
% 0.60/0.79             ( ( m1_pre_topc @ C @ A ) =>
% 0.60/0.79               ( ![D:$i]:
% 0.60/0.79                 ( ( m1_pre_topc @ D @ A ) =>
% 0.60/0.79                   ( ![E:$i]:
% 0.60/0.79                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.79                         ( v1_funct_2 @
% 0.60/0.79                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                         ( m1_subset_1 @
% 0.60/0.79                           E @ 
% 0.60/0.79                           ( k1_zfmisc_1 @
% 0.60/0.79                             ( k2_zfmisc_1 @
% 0.60/0.79                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79                       ( ( m1_pre_topc @ D @ C ) =>
% 0.60/0.79                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.60/0.79                           ( k2_partfun1 @
% 0.60/0.79                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.60/0.79                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X4)
% 0.60/0.79          | ~ (v2_pre_topc @ X4)
% 0.60/0.79          | ~ (l1_pre_topc @ X4)
% 0.60/0.79          | ~ (m1_pre_topc @ X5 @ X6)
% 0.60/0.79          | ~ (m1_pre_topc @ X5 @ X7)
% 0.60/0.79          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 0.60/0.79                 (u1_struct_0 @ X5)))
% 0.60/0.79          | ~ (m1_subset_1 @ X8 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 0.60/0.79          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 0.60/0.79          | ~ (v1_funct_1 @ X8)
% 0.60/0.79          | ~ (m1_pre_topc @ X7 @ X6)
% 0.60/0.79          | ~ (l1_pre_topc @ X6)
% 0.60/0.79          | ~ (v2_pre_topc @ X6)
% 0.60/0.79          | (v2_struct_0 @ X6))),
% 0.60/0.79      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.79          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X1)))
% 0.60/0.79          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.79  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('21', plain,
% 0.60/0.79      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.79          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X1)))
% 0.60/0.79          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_B)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['16', '24'])).
% 0.60/0.79  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_B)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_A)
% 0.60/0.79          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.79  thf('31', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_B)
% 0.60/0.79        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_A)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['15', '30'])).
% 0.60/0.79  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('33', plain,
% 0.60/0.79      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.79      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_E @ 
% 0.60/0.79        (k1_zfmisc_1 @ 
% 0.60/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(d4_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.79             ( l1_pre_topc @ B ) ) =>
% 0.60/0.79           ( ![C:$i]:
% 0.60/0.79             ( ( ( v1_funct_1 @ C ) & 
% 0.60/0.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                 ( m1_subset_1 @
% 0.60/0.79                   C @ 
% 0.60/0.79                   ( k1_zfmisc_1 @
% 0.60/0.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79               ( ![D:$i]:
% 0.60/0.79                 ( ( m1_pre_topc @ D @ A ) =>
% 0.60/0.79                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.60/0.79                     ( k2_partfun1 @
% 0.60/0.79                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.60/0.79                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf('35', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ X1 @ X2)
% 0.60/0.79          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.60/0.79                 (u1_struct_0 @ X1)))
% 0.60/0.79          | ~ (m1_subset_1 @ X3 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.60/0.79          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.60/0.79          | ~ (v1_funct_1 @ X3)
% 0.60/0.79          | ~ (l1_pre_topc @ X2)
% 0.60/0.79          | ~ (v2_pre_topc @ X2)
% 0.60/0.79          | (v2_struct_0 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.79          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.79  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('39', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('40', plain,
% 0.60/0.79      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('43', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_A)
% 0.60/0.79          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)],
% 0.60/0.79                ['36', '37', '38', '39', '40', '41', '42'])).
% 0.60/0.79  thf('44', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_B)
% 0.60/0.79        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_A)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['33', '43'])).
% 0.60/0.79  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('46', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_A)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['44', '45'])).
% 0.60/0.79  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('48', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_A))))),
% 0.60/0.79      inference('clc', [status(thm)], ['46', '47'])).
% 0.60/0.79  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('50', plain,
% 0.60/0.79      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.60/0.79         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79            (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['48', '49'])).
% 0.60/0.79  thf('51', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.60/0.79            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['31', '32', '50'])).
% 0.60/0.79  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('53', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.60/0.79            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['51', '52'])).
% 0.60/0.79  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('55', plain,
% 0.60/0.79      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.60/0.79         = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))),
% 0.60/0.79      inference('clc', [status(thm)], ['53', '54'])).
% 0.60/0.79  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('58', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))
% 0.60/0.79        | (v2_struct_0 @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['13', '14', '55', '56', '57'])).
% 0.60/0.79  thf('59', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))
% 0.60/0.79        | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('simplify', [status(thm)], ['58'])).
% 0.60/0.79  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('61', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['59', '60'])).
% 0.60/0.79  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('63', plain,
% 0.60/0.79      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79        (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))),
% 0.60/0.79      inference('clc', [status(thm)], ['61', '62'])).
% 0.60/0.79  thf('64', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_E @ 
% 0.60/0.79        (k1_zfmisc_1 @ 
% 0.60/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t77_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.79             ( l1_pre_topc @ B ) ) =>
% 0.60/0.79           ( ![C:$i]:
% 0.60/0.79             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.79               ( ![D:$i]:
% 0.60/0.79                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.79                   ( ![E:$i]:
% 0.60/0.79                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.79                         ( v1_funct_2 @
% 0.60/0.79                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                         ( m1_subset_1 @
% 0.60/0.79                           E @ 
% 0.60/0.79                           ( k1_zfmisc_1 @
% 0.60/0.79                             ( k2_zfmisc_1 @
% 0.60/0.79                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79                       ( ![F:$i]:
% 0.60/0.79                         ( ( ( v1_funct_1 @ F ) & 
% 0.60/0.79                             ( v1_funct_2 @
% 0.60/0.79                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79                             ( m1_subset_1 @
% 0.60/0.79                               F @ 
% 0.60/0.79                               ( k1_zfmisc_1 @
% 0.60/0.79                                 ( k2_zfmisc_1 @
% 0.60/0.79                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79                           ( ( ( r2_funct_2 @
% 0.60/0.79                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.60/0.79                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.60/0.79                               ( m1_pre_topc @ D @ C ) ) =>
% 0.60/0.79                             ( r2_funct_2 @
% 0.60/0.79                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.60/0.79                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.60/0.79                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf('65', plain,
% 0.60/0.79      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X19)
% 0.60/0.79          | ~ (v2_pre_topc @ X19)
% 0.60/0.79          | ~ (l1_pre_topc @ X19)
% 0.60/0.79          | (v2_struct_0 @ X20)
% 0.60/0.79          | ~ (m1_pre_topc @ X20 @ X21)
% 0.60/0.79          | ~ (v1_funct_1 @ X22)
% 0.60/0.79          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))
% 0.60/0.79          | ~ (m1_subset_1 @ X22 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))))
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ 
% 0.60/0.79             (k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X22) @ 
% 0.60/0.79             (k2_tmap_1 @ X21 @ X19 @ X24 @ X20))
% 0.60/0.79          | ~ (r2_funct_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19) @ X22 @ 
% 0.60/0.79               (k2_tmap_1 @ X21 @ X19 @ X24 @ X23))
% 0.60/0.79          | ~ (m1_pre_topc @ X20 @ X23)
% 0.60/0.79          | ~ (m1_subset_1 @ X24 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.60/0.79          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.60/0.79          | ~ (v1_funct_1 @ X24)
% 0.60/0.79          | ~ (m1_pre_topc @ X23 @ X21)
% 0.60/0.79          | (v2_struct_0 @ X23)
% 0.60/0.79          | ~ (l1_pre_topc @ X21)
% 0.60/0.79          | ~ (v2_pre_topc @ X21)
% 0.60/0.79          | (v2_struct_0 @ X21))),
% 0.60/0.79      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.60/0.79  thf('66', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X1)
% 0.60/0.79          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ~ (m1_subset_1 @ X1 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.79          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.60/0.79          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A))
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.60/0.79          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.79          | ~ (m1_pre_topc @ X2 @ X0)
% 0.60/0.79          | (v2_struct_0 @ X2)
% 0.60/0.79          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['64', '65'])).
% 0.60/0.79  thf('67', plain,
% 0.60/0.79      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('71', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.79          | ~ (v1_funct_1 @ X1)
% 0.60/0.79          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ~ (m1_subset_1 @ X1 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.79          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.60/0.79          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A))
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.60/0.79          | ~ (m1_pre_topc @ X2 @ X0)
% 0.60/0.79          | (v2_struct_0 @ X2)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.60/0.79  thf('72', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ~ (m1_subset_1 @ sk_E @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.79                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.60/0.79          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.79          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['63', '71'])).
% 0.60/0.79  thf('73', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_E @ 
% 0.60/0.79        (k1_zfmisc_1 @ 
% 0.60/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('74', plain,
% 0.60/0.79      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('78', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['72', '73', '74', '75', '76', '77'])).
% 0.60/0.79  thf('79', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_A)
% 0.60/0.79          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('simplify', [status(thm)], ['78'])).
% 0.60/0.79  thf('80', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.79          | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['3', '79'])).
% 0.60/0.79  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('82', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_B)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.79             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.79          | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['80', '81'])).
% 0.60/0.79  thf('83', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.79           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.79        | (v2_struct_0 @ sk_D)
% 0.60/0.79        | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['2', '82'])).
% 0.60/0.79  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('85', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_A)
% 0.60/0.79          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.79  thf('86', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_D)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['84', '85'])).
% 0.60/0.79  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('88', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.60/0.79      inference('clc', [status(thm)], ['86', '87'])).
% 0.60/0.79  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('90', plain,
% 0.60/0.79      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.60/0.79         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79            (u1_struct_0 @ sk_D)))),
% 0.60/0.79      inference('clc', [status(thm)], ['88', '89'])).
% 0.60/0.79  thf('91', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('92', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ sk_A)
% 0.60/0.79          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.60/0.79              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.79          | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)],
% 0.60/0.79                ['36', '37', '38', '39', '40', '41', '42'])).
% 0.60/0.79  thf('93', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_D)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['91', '92'])).
% 0.60/0.79  thf('94', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('95', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.79            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.60/0.79      inference('clc', [status(thm)], ['93', '94'])).
% 0.60/0.79  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('97', plain,
% 0.60/0.79      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.79         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.79            (u1_struct_0 @ sk_D)))),
% 0.60/0.79      inference('clc', [status(thm)], ['95', '96'])).
% 0.60/0.79  thf('98', plain,
% 0.60/0.79      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.79         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.79      inference('sup+', [status(thm)], ['90', '97'])).
% 0.60/0.79  thf('99', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.79           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.79        | (v2_struct_0 @ sk_D)
% 0.60/0.79        | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['83', '98'])).
% 0.60/0.79  thf('100', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('101', plain,
% 0.60/0.79      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.79      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.79  thf('102', plain,
% 0.60/0.79      ((m1_subset_1 @ sk_E @ 
% 0.60/0.79        (k1_zfmisc_1 @ 
% 0.60/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(dt_k3_tmap_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.79         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.60/0.79         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.60/0.79         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.60/0.79         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.79         ( m1_subset_1 @
% 0.60/0.79           E @ 
% 0.60/0.79           ( k1_zfmisc_1 @
% 0.60/0.79             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.79       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.60/0.79         ( v1_funct_2 @
% 0.60/0.79           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.60/0.79           ( u1_struct_0 @ B ) ) & 
% 0.60/0.79         ( m1_subset_1 @
% 0.60/0.79           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.60/0.79           ( k1_zfmisc_1 @
% 0.60/0.79             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.60/0.79  thf('103', plain,
% 0.60/0.79      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.79         (~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.79          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.79          | ~ (l1_pre_topc @ X12)
% 0.60/0.79          | ~ (v2_pre_topc @ X12)
% 0.60/0.79          | (v2_struct_0 @ X12)
% 0.60/0.79          | ~ (l1_pre_topc @ X10)
% 0.60/0.79          | ~ (v2_pre_topc @ X10)
% 0.60/0.79          | (v2_struct_0 @ X10)
% 0.60/0.79          | ~ (v1_funct_1 @ X13)
% 0.60/0.79          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12))
% 0.60/0.79          | ~ (m1_subset_1 @ X13 @ 
% 0.60/0.79               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12))))
% 0.60/0.80          | (m1_subset_1 @ (k3_tmap_1 @ X10 @ X12 @ X11 @ X9 @ X13) @ 
% 0.60/0.80             (k1_zfmisc_1 @ 
% 0.60/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X12)))))),
% 0.60/0.80      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.80  thf('104', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80           (k1_zfmisc_1 @ 
% 0.60/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.80          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.80          | (v2_struct_0 @ X1)
% 0.60/0.80          | ~ (v2_pre_topc @ X1)
% 0.60/0.80          | ~ (l1_pre_topc @ X1)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.80      inference('sup-', [status(thm)], ['102', '103'])).
% 0.60/0.80  thf('105', plain,
% 0.60/0.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('109', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80           (k1_zfmisc_1 @ 
% 0.60/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.80          | (v2_struct_0 @ X1)
% 0.60/0.80          | ~ (v2_pre_topc @ X1)
% 0.60/0.80          | ~ (l1_pre_topc @ X1)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.80      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.60/0.80  thf('110', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80             (k1_zfmisc_1 @ 
% 0.60/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.80      inference('sup-', [status(thm)], ['101', '109'])).
% 0.60/0.80  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('114', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80             (k1_zfmisc_1 @ 
% 0.60/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.80      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.60/0.80  thf('115', plain,
% 0.60/0.80      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.80         (k1_zfmisc_1 @ 
% 0.60/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['100', '114'])).
% 0.60/0.80  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('117', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_B)
% 0.60/0.80        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.80           (k1_zfmisc_1 @ 
% 0.60/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.80      inference('clc', [status(thm)], ['115', '116'])).
% 0.60/0.80  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('119', plain,
% 0.60/0.80      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.80        (k1_zfmisc_1 @ 
% 0.60/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.80      inference('clc', [status(thm)], ['117', '118'])).
% 0.60/0.80  thf('120', plain,
% 0.60/0.80      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.80         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.80      inference('sup+', [status(thm)], ['90', '97'])).
% 0.60/0.80  thf('121', plain,
% 0.60/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80        (k1_zfmisc_1 @ 
% 0.60/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.80      inference('demod', [status(thm)], ['119', '120'])).
% 0.60/0.80  thf('122', plain,
% 0.60/0.80      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.80         ((v2_struct_0 @ X19)
% 0.60/0.80          | ~ (v2_pre_topc @ X19)
% 0.60/0.80          | ~ (l1_pre_topc @ X19)
% 0.60/0.80          | (v2_struct_0 @ X20)
% 0.60/0.80          | ~ (m1_pre_topc @ X20 @ X21)
% 0.60/0.80          | ~ (v1_funct_1 @ X22)
% 0.60/0.80          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))
% 0.60/0.80          | ~ (m1_subset_1 @ X22 @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))))
% 0.60/0.80          | (r2_funct_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ 
% 0.60/0.80             (k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X22) @ 
% 0.60/0.80             (k2_tmap_1 @ X21 @ X19 @ X24 @ X20))
% 0.60/0.80          | ~ (r2_funct_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19) @ X22 @ 
% 0.60/0.80               (k2_tmap_1 @ X21 @ X19 @ X24 @ X23))
% 0.60/0.80          | ~ (m1_pre_topc @ X20 @ X23)
% 0.60/0.80          | ~ (m1_subset_1 @ X24 @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.60/0.80          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.60/0.80          | ~ (v1_funct_1 @ X24)
% 0.60/0.80          | ~ (m1_pre_topc @ X23 @ X21)
% 0.60/0.80          | (v2_struct_0 @ X23)
% 0.60/0.80          | ~ (l1_pre_topc @ X21)
% 0.60/0.80          | ~ (v2_pre_topc @ X21)
% 0.60/0.80          | (v2_struct_0 @ X21))),
% 0.60/0.80      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.60/0.80  thf('123', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((v2_struct_0 @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.80          | ~ (v1_funct_1 @ X1)
% 0.60/0.80          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (m1_subset_1 @ X1 @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.80          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.60/0.80          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.60/0.80          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.60/0.80              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.60/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.80          | ~ (m1_pre_topc @ X2 @ X0)
% 0.60/0.80          | (v2_struct_0 @ X2)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['121', '122'])).
% 0.60/0.80  thf('124', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('125', plain,
% 0.60/0.80      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.80  thf('126', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_E @ 
% 0.60/0.80        (k1_zfmisc_1 @ 
% 0.60/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('127', plain,
% 0.60/0.80      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.80         (~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.80          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.80          | ~ (l1_pre_topc @ X12)
% 0.60/0.80          | ~ (v2_pre_topc @ X12)
% 0.60/0.80          | (v2_struct_0 @ X12)
% 0.60/0.80          | ~ (l1_pre_topc @ X10)
% 0.60/0.80          | ~ (v2_pre_topc @ X10)
% 0.60/0.80          | (v2_struct_0 @ X10)
% 0.60/0.80          | ~ (v1_funct_1 @ X13)
% 0.60/0.80          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12))
% 0.60/0.80          | ~ (m1_subset_1 @ X13 @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12))))
% 0.60/0.80          | (v1_funct_2 @ (k3_tmap_1 @ X10 @ X12 @ X11 @ X9 @ X13) @ 
% 0.60/0.80             (u1_struct_0 @ X9) @ (u1_struct_0 @ X12)))),
% 0.60/0.80      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.80  thf('128', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.80          | (v2_struct_0 @ X1)
% 0.60/0.80          | ~ (v2_pre_topc @ X1)
% 0.60/0.80          | ~ (l1_pre_topc @ X1)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.80      inference('sup-', [status(thm)], ['126', '127'])).
% 0.60/0.80  thf('129', plain,
% 0.60/0.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('131', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('132', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('133', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | (v2_struct_0 @ X1)
% 0.60/0.80          | ~ (v2_pre_topc @ X1)
% 0.60/0.80          | ~ (l1_pre_topc @ X1)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.80      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.60/0.80  thf('134', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['125', '133'])).
% 0.60/0.80  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('138', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.80             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.80      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 0.60/0.80  thf('139', plain,
% 0.60/0.80      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.80         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['124', '138'])).
% 0.60/0.80  thf('140', plain,
% 0.60/0.80      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.80         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.80      inference('sup+', [status(thm)], ['90', '97'])).
% 0.60/0.80  thf('141', plain,
% 0.60/0.80      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['139', '140'])).
% 0.60/0.80  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('143', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_B)
% 0.60/0.80        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.80      inference('clc', [status(thm)], ['141', '142'])).
% 0.60/0.80  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('145', plain,
% 0.60/0.80      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.80      inference('clc', [status(thm)], ['143', '144'])).
% 0.60/0.80  thf('146', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('147', plain,
% 0.60/0.80      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.80  thf('148', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_E @ 
% 0.60/0.80        (k1_zfmisc_1 @ 
% 0.60/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('149', plain,
% 0.60/0.80      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.80         (~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.80          | ~ (m1_pre_topc @ X11 @ X10)
% 0.60/0.80          | ~ (l1_pre_topc @ X12)
% 0.60/0.80          | ~ (v2_pre_topc @ X12)
% 0.60/0.80          | (v2_struct_0 @ X12)
% 0.60/0.80          | ~ (l1_pre_topc @ X10)
% 0.60/0.80          | ~ (v2_pre_topc @ X10)
% 0.60/0.80          | (v2_struct_0 @ X10)
% 0.60/0.80          | ~ (v1_funct_1 @ X13)
% 0.60/0.80          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12))
% 0.60/0.80          | ~ (m1_subset_1 @ X13 @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12))))
% 0.60/0.80          | (v1_funct_1 @ (k3_tmap_1 @ X10 @ X12 @ X11 @ X9 @ X13)))),
% 0.60/0.80      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.80  thf('150', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.60/0.80          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.80          | (v2_struct_0 @ X1)
% 0.60/0.80          | ~ (v2_pre_topc @ X1)
% 0.60/0.80          | ~ (l1_pre_topc @ X1)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.80      inference('sup-', [status(thm)], ['148', '149'])).
% 0.60/0.80  thf('151', plain,
% 0.60/0.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('152', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('153', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('154', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('155', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.60/0.80          | (v2_struct_0 @ X1)
% 0.60/0.80          | ~ (v2_pre_topc @ X1)
% 0.60/0.80          | ~ (l1_pre_topc @ X1)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.80      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 0.60/0.80  thf('156', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['147', '155'])).
% 0.60/0.80  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('160', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.60/0.80      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.60/0.80  thf('161', plain,
% 0.60/0.80      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['146', '160'])).
% 0.60/0.80  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('163', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_B)
% 0.60/0.80        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.60/0.80      inference('clc', [status(thm)], ['161', '162'])).
% 0.60/0.80  thf('164', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('165', plain,
% 0.60/0.80      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.80      inference('clc', [status(thm)], ['163', '164'])).
% 0.60/0.80  thf('166', plain,
% 0.60/0.80      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.80         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.80      inference('sup+', [status(thm)], ['90', '97'])).
% 0.60/0.80  thf('167', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.60/0.80      inference('demod', [status(thm)], ['165', '166'])).
% 0.60/0.80  thf('168', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('169', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('170', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((v2_struct_0 @ X0)
% 0.60/0.80          | ~ (v2_pre_topc @ X0)
% 0.60/0.80          | ~ (l1_pre_topc @ X0)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.80          | ~ (v1_funct_1 @ X1)
% 0.60/0.80          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (m1_subset_1 @ X1 @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.80          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.60/0.80          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.80               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.60/0.80          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.60/0.80              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.60/0.80          | ~ (m1_pre_topc @ X2 @ X0)
% 0.60/0.80          | (v2_struct_0 @ X2)
% 0.60/0.80          | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['123', '145', '167', '168', '169'])).
% 0.60/0.80  thf('171', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.80              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.80          | ~ (m1_subset_1 @ sk_E @ 
% 0.60/0.80               (k1_zfmisc_1 @ 
% 0.60/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.60/0.80          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.80          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.80          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['99', '170'])).
% 0.60/0.80  thf('172', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_E @ 
% 0.60/0.80        (k1_zfmisc_1 @ 
% 0.60/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('173', plain,
% 0.60/0.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('174', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('175', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('178', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_B)
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.80              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('demod', [status(thm)],
% 0.60/0.80                ['171', '172', '173', '174', '175', '176', '177'])).
% 0.60/0.80  thf('179', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.80          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.80              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ X0)
% 0.60/0.80          | (v2_struct_0 @ sk_A)
% 0.60/0.80          | (v2_struct_0 @ sk_D)
% 0.60/0.80          | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('simplify', [status(thm)], ['178'])).
% 0.60/0.80  thf('180', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_B)
% 0.60/0.80        | (v2_struct_0 @ sk_D)
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_C)
% 0.60/0.80        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.60/0.80        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.80            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['1', '179'])).
% 0.60/0.80  thf('181', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('182', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_B)
% 0.60/0.80        | (v2_struct_0 @ sk_D)
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_C)
% 0.60/0.80        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.80            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.60/0.80      inference('demod', [status(thm)], ['180', '181'])).
% 0.60/0.80  thf('183', plain,
% 0.60/0.80      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.80          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.80           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.80          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('184', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_C)
% 0.60/0.80        | (v2_struct_0 @ sk_A)
% 0.60/0.80        | (v2_struct_0 @ sk_D)
% 0.60/0.80        | (v2_struct_0 @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['182', '183'])).
% 0.60/0.80  thf('185', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('186', plain,
% 0.60/0.80      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.60/0.80      inference('sup-', [status(thm)], ['184', '185'])).
% 0.60/0.80  thf('187', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('188', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.60/0.80      inference('clc', [status(thm)], ['186', '187'])).
% 0.60/0.80  thf('189', plain, (~ (v2_struct_0 @ sk_C)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('190', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.80      inference('clc', [status(thm)], ['188', '189'])).
% 0.60/0.80  thf('191', plain, ($false), inference('demod', [status(thm)], ['0', '190'])).
% 0.60/0.80  
% 0.60/0.80  % SZS output end Refutation
% 0.60/0.80  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
