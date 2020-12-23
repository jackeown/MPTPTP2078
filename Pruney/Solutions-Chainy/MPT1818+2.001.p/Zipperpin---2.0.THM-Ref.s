%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H6vV4GZhRp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:09 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  467 (14365 expanded)
%              Number of leaves         :   28 (4071 expanded)
%              Depth                    :   26
%              Number of atoms          : 7445 (1161862 expanded)
%              Number of equality atoms :   86 (9065 expanded)
%              Maximal formula depth    :   30 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(t134_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( v1_tsep_1 @ E @ A )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( A
                          = ( k1_tsep_1 @ A @ D @ E ) )
                       => ( ( ( v1_funct_1 @ C )
                            & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ C @ A @ B )
                            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_tsep_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( v1_tsep_1 @ E @ A )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                         => ( ( ( v1_funct_1 @ C )
                              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ C @ A @ B )
                              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                          <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                              & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('4',plain,(
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

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('24',plain,(
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

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('39',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t126_tmap_1,axiom,(
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
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ X13 @ X9 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ sk_E @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_tsep_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_tsep_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r4_tsep_1 @ X16 @ X15 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v1_tsep_1 @ X17 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_tsep_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ sk_E @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','57','58','59','60','61','62','63','64','65','66','67','68'])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85','86'])).

thf('88',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','89'])).

thf('91',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95'])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('113',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121'])).

thf('123',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('126',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','140','141','142','143','144'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['109','145'])).

thf('147',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['98'])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ X13 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('161',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ X13 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','161'])).

thf('163',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','167','168','169'])).

thf('171',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['158','172'])).

thf('174',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('175',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['173','174','175','176','177','178'])).

thf('180',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['157','179'])).

thf('181',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['98'])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('192',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('195',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','195'])).

thf('197',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('202',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197','198','199','200','201','202','203','204'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['192','205'])).

thf('207',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('208',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['206','207','208','209','210','211'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['191','212'])).

thf('214',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('228',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ sk_E @ X0 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['226','228'])).

thf('230',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('235',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ sk_E @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233','234','235','236','237'])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['225','238'])).

thf('240',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('241',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['239','240','241','242','243','244'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['224','245'])).

thf('247',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['98'])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('258',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('261',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','261'])).

thf('263',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['262','263','264','265','266','267','268','269'])).

thf('271',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['258','272'])).

thf('274',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('275',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['273','274','275','276','277','278'])).

thf('280',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['257','279'])).

thf('281',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['98'])).

thf('282',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['286','287'])).

thf('289',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('292',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('295',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['293','295'])).

thf('297',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['296','297','298','299','300','301','302','303'])).

thf('305',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('306',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['292','306'])).

thf('308',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('309',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['307','308','309','310','311','312'])).

thf('314',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['291','313'])).

thf('315',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['98'])).

thf('316',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['318','319'])).

thf('321',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['320','321'])).

thf('323',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['98'])).

thf('327',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['98'])).

thf('330',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('333',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('335',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('338',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['336','338'])).

thf('340',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['339','340','341','342','343','344','345','346'])).

thf('348',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(clc,[status(thm)],['55','56'])).

thf('349',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['335','349'])).

thf('351',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('352',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['350','351','352','353','354','355'])).

thf('357',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['334','356'])).

thf('358',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['98'])).

thf('359',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['359','360'])).

thf('362',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['361','362'])).

thf('364',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['363','364'])).

thf('366',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('368',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('369',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['369'])).

thf('371',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','370'])).

thf('372',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['72','371'])).

thf('373',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('376',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['376'])).

thf('378',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('379',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','378'])).

thf('380',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['377','379'])).

thf('381',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('382',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['382'])).

thf('384',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['384'])).

thf('386',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','385'])).

thf('387',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['383','386'])).

thf('388',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('389',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('390',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['389'])).

thf('391',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['391'])).

thf('393',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','392'])).

thf('394',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['390','393'])).

thf('395',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('396',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['396'])).

thf('398',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['398'])).

thf('400',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','399'])).

thf('401',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['397','400'])).

thf('402',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('403',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['403'])).

thf('405',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('406',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['405'])).

thf('407',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','406'])).

thf('408',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['404','407'])).

thf('409',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('410',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['410'])).

thf('412',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('413',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['412'])).

thf('414',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','413'])).

thf('415',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['411','414'])).

thf('416',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('417',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['417'])).

thf('419',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('420',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['419'])).

thf('421',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368','420'])).

thf('422',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['418','421'])).

thf('423',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','372','373','374','375','380','381','387','388','394','395','401','402','408','409','415','416','422','423','424','425'])).

thf('427',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['98'])).

thf('428',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['108','156','190','223','256','290','324','327','330','333','367','368'])).

thf('429',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['427','428'])).

thf('430',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['426','429'])).

thf('431',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('432',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['430','431'])).

thf('433',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['432','433'])).

thf('435',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['434','435'])).

thf('437',plain,(
    $false ),
    inference(demod,[status(thm)],['0','436'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H6vV4GZhRp
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:49:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 270 iterations in 0.119s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.60  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.38/0.60  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.38/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.60  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.60  thf(t134_tmap_1, conjecture,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                 ( m1_subset_1 @
% 0.38/0.60                   C @ 
% 0.38/0.60                   ( k1_zfmisc_1 @
% 0.38/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.38/0.60                     ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.60                   ( ![E:$i]:
% 0.38/0.60                     ( ( ( ~( v2_struct_0 @ E ) ) & ( v1_tsep_1 @ E @ A ) & 
% 0.38/0.60                         ( m1_pre_topc @ E @ A ) ) =>
% 0.38/0.60                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.38/0.60                         ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                             ( v1_funct_2 @
% 0.38/0.60                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                             ( v5_pre_topc @ C @ A @ B ) & 
% 0.38/0.60                             ( m1_subset_1 @
% 0.38/0.60                               C @ 
% 0.38/0.60                               ( k1_zfmisc_1 @
% 0.38/0.60                                 ( k2_zfmisc_1 @
% 0.38/0.60                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.38/0.60                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.60                             ( v1_funct_2 @
% 0.38/0.60                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.38/0.60                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                             ( v5_pre_topc @
% 0.38/0.60                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.38/0.60                             ( m1_subset_1 @
% 0.38/0.60                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.38/0.60                               ( k1_zfmisc_1 @
% 0.38/0.60                                 ( k2_zfmisc_1 @
% 0.38/0.60                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.38/0.60                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.38/0.60                             ( v1_funct_2 @
% 0.38/0.60                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.38/0.60                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                             ( v5_pre_topc @
% 0.38/0.60                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.38/0.60                             ( m1_subset_1 @
% 0.38/0.60                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.38/0.60                               ( k1_zfmisc_1 @
% 0.38/0.60                                 ( k2_zfmisc_1 @
% 0.38/0.60                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]:
% 0.38/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.60            ( l1_pre_topc @ A ) ) =>
% 0.38/0.60          ( ![B:$i]:
% 0.38/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60                ( l1_pre_topc @ B ) ) =>
% 0.38/0.60              ( ![C:$i]:
% 0.38/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                    ( v1_funct_2 @
% 0.38/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                    ( m1_subset_1 @
% 0.38/0.60                      C @ 
% 0.38/0.60                      ( k1_zfmisc_1 @
% 0.38/0.60                        ( k2_zfmisc_1 @
% 0.38/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60                  ( ![D:$i]:
% 0.38/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.38/0.60                        ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.60                      ( ![E:$i]:
% 0.38/0.60                        ( ( ( ~( v2_struct_0 @ E ) ) & ( v1_tsep_1 @ E @ A ) & 
% 0.38/0.60                            ( m1_pre_topc @ E @ A ) ) =>
% 0.38/0.60                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.38/0.60                            ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                                ( v1_funct_2 @
% 0.38/0.60                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                                ( v5_pre_topc @ C @ A @ B ) & 
% 0.38/0.60                                ( m1_subset_1 @
% 0.38/0.60                                  C @ 
% 0.38/0.60                                  ( k1_zfmisc_1 @
% 0.38/0.60                                    ( k2_zfmisc_1 @
% 0.38/0.60                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.38/0.60                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.60                                ( v1_funct_2 @
% 0.38/0.60                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.38/0.60                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                                ( v5_pre_topc @
% 0.38/0.60                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.38/0.60                                ( m1_subset_1 @
% 0.38/0.60                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.38/0.60                                  ( k1_zfmisc_1 @
% 0.38/0.60                                    ( k2_zfmisc_1 @
% 0.38/0.60                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.38/0.60                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.38/0.60                                ( v1_funct_2 @
% 0.38/0.60                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.38/0.60                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                                ( v5_pre_topc @
% 0.38/0.60                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.38/0.60                                ( m1_subset_1 @
% 0.38/0.60                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.38/0.60                                  ( k1_zfmisc_1 @
% 0.38/0.60                                    ( k2_zfmisc_1 @
% 0.38/0.60                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t134_tmap_1])).
% 0.38/0.60  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t2_tsep_1, axiom,
% 0.38/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.38/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(d5_tmap_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_pre_topc @ C @ A ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( m1_pre_topc @ D @ A ) =>
% 0.38/0.60                   ( ![E:$i]:
% 0.38/0.60                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.60                         ( v1_funct_2 @
% 0.38/0.60                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                         ( m1_subset_1 @
% 0.38/0.60                           E @ 
% 0.38/0.60                           ( k1_zfmisc_1 @
% 0.38/0.60                             ( k2_zfmisc_1 @
% 0.38/0.60                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60                       ( ( m1_pre_topc @ D @ C ) =>
% 0.38/0.60                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.38/0.60                           ( k2_partfun1 @
% 0.38/0.60                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.38/0.60                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X4)
% 0.38/0.60          | ~ (v2_pre_topc @ X4)
% 0.38/0.60          | ~ (l1_pre_topc @ X4)
% 0.38/0.60          | ~ (m1_pre_topc @ X5 @ X6)
% 0.38/0.60          | ~ (m1_pre_topc @ X5 @ X7)
% 0.38/0.60          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 0.38/0.60                 (u1_struct_0 @ X5)))
% 0.38/0.60          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 0.38/0.60          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 0.38/0.60          | ~ (v1_funct_1 @ X8)
% 0.38/0.60          | ~ (m1_pre_topc @ X7 @ X6)
% 0.38/0.60          | ~ (l1_pre_topc @ X6)
% 0.38/0.60          | ~ (v2_pre_topc @ X6)
% 0.38/0.60          | (v2_struct_0 @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.38/0.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.38/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_B)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '10'])).
% 0.38/0.60  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_B)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_D)))
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '16'])).
% 0.38/0.60  thf('18', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_D))))),
% 0.38/0.60      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.38/0.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.60            (u1_struct_0 @ sk_D)))),
% 0.38/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.60  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(d4_tmap_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                 ( m1_subset_1 @
% 0.38/0.60                   C @ 
% 0.38/0.60                   ( k1_zfmisc_1 @
% 0.38/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( m1_pre_topc @ D @ A ) =>
% 0.38/0.60                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.38/0.60                     ( k2_partfun1 @
% 0.38/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.38/0.60                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ X1 @ X2)
% 0.38/0.60          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.38/0.60                 (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (m1_subset_1 @ X3 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X3)
% 0.38/0.60          | ~ (l1_pre_topc @ X2)
% 0.38/0.60          | ~ (v2_pre_topc @ X2)
% 0.38/0.60          | (v2_struct_0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.60  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['25', '26', '27', '28', '29', '30', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_D)))
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['22', '32'])).
% 0.38/0.60  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_D))))),
% 0.38/0.60      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.60  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.60            (u1_struct_0 @ sk_D)))),
% 0.38/0.60      inference('clc', [status(thm)], ['35', '36'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.60      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.60  thf('39', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t126_tmap_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.60             ( l1_pre_topc @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.60                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.38/0.60                     ( ![E:$i]:
% 0.38/0.60                       ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.60                           ( v1_funct_2 @
% 0.38/0.60                             E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.60                             ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                           ( m1_subset_1 @
% 0.38/0.60                             E @ 
% 0.38/0.60                             ( k1_zfmisc_1 @
% 0.38/0.60                               ( k2_zfmisc_1 @
% 0.38/0.60                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.60                                 ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60                         ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.60                             ( v1_funct_2 @
% 0.38/0.60                               E @ 
% 0.38/0.60                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.60                               ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                             ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.38/0.60                             ( m1_subset_1 @
% 0.38/0.60                               E @ 
% 0.38/0.60                               ( k1_zfmisc_1 @
% 0.38/0.60                                 ( k2_zfmisc_1 @
% 0.38/0.60                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.60                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.38/0.60                           ( ( v1_funct_1 @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) ) & 
% 0.38/0.60                             ( v1_funct_2 @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.38/0.60                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                             ( v5_pre_topc @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.38/0.60                               C @ B ) & 
% 0.38/0.60                             ( m1_subset_1 @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.38/0.60                               ( k1_zfmisc_1 @
% 0.38/0.60                                 ( k2_zfmisc_1 @
% 0.38/0.60                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.38/0.60                             ( v1_funct_1 @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) & 
% 0.38/0.60                             ( v1_funct_2 @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.38/0.60                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                             ( v5_pre_topc @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.38/0.60                               D @ B ) & 
% 0.38/0.60                             ( m1_subset_1 @
% 0.38/0.60                               ( k3_tmap_1 @
% 0.38/0.60                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.38/0.60                               ( k1_zfmisc_1 @
% 0.38/0.60                                 ( k2_zfmisc_1 @
% 0.38/0.60                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | ~ (v1_funct_1 @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.38/0.60                X12))
% 0.38/0.60          | ~ (v1_funct_2 @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.38/0.60                X12) @ 
% 0.38/0.60               (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v5_pre_topc @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.38/0.60                X12) @ 
% 0.38/0.60               X13 @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.38/0.60                X12) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v1_funct_1 @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.38/0.60                X12))
% 0.38/0.60          | ~ (v1_funct_2 @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.38/0.60                X12) @ 
% 0.38/0.60               (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v5_pre_topc @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.38/0.60                X12) @ 
% 0.38/0.60               X10 @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ 
% 0.38/0.60               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.38/0.60                X12) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))))
% 0.38/0.60          | (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.60               (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ 
% 0.38/0.60                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.60                 (u1_struct_0 @ X0))))
% 0.38/0.60          | (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_E @ X1) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | ~ (v5_pre_topc @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_E @ X1) @ 
% 0.38/0.60               sk_E @ X0)
% 0.38/0.60          | ~ (v1_funct_2 @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_E @ X1) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_E @ X1))
% 0.38/0.60          | ~ (v5_pre_topc @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_D @ X1) @ 
% 0.38/0.60               sk_D @ X0)
% 0.38/0.60          | ~ (v1_funct_2 @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_D @ X1) @ 
% 0.38/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ 
% 0.38/0.60               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60                sk_D @ X1))
% 0.38/0.60          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('45', plain, ((v1_tsep_1 @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('46', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t88_tsep_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.60               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         (~ (v1_tsep_1 @ X15 @ X16)
% 0.38/0.60          | ~ (m1_pre_topc @ X15 @ X16)
% 0.38/0.60          | (r4_tsep_1 @ X16 @ X15 @ X17)
% 0.38/0.60          | ~ (m1_pre_topc @ X17 @ X16)
% 0.38/0.60          | ~ (v1_tsep_1 @ X17 @ X16)
% 0.38/0.60          | ~ (l1_pre_topc @ X16)
% 0.38/0.60          | ~ (v2_pre_topc @ X16)
% 0.38/0.60          | (v2_struct_0 @ X16))),
% 0.38/0.60      inference('cnf', [status(esa)], [t88_tsep_1])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.60  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('51', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | (r4_tsep_1 @ sk_A @ sk_D @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      (((r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.60        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '52'])).
% 0.38/0.60  thf('54', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('55', plain, (((r4_tsep_1 @ sk_A @ sk_D @ sk_E) | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.60  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('57', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('58', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('59', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('60', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('61', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('62', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('63', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('64', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('65', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('66', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('67', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('68', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('69', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.38/0.60               sk_E @ X0)
% 0.38/0.60          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1))
% 0.38/0.60          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.60               sk_D @ X0)
% 0.38/0.60          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1))
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['41', '42', '43', '44', '57', '58', '59', '60', '61', '62', 
% 0.38/0.60                 '63', '64', '65', '66', '67', '68'])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60           (k1_zfmisc_1 @ 
% 0.38/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | (v2_struct_0 @ sk_B)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_E)
% 0.38/0.60        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 0.38/0.60        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.38/0.60             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.38/0.60             sk_D @ sk_B)
% 0.38/0.60        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 0.38/0.60        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.38/0.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.38/0.60             sk_E @ sk_B)
% 0.38/0.60        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (m1_subset_1 @ sk_C @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | (v2_struct_0 @ sk_D)
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['38', '69'])).
% 0.38/0.60  thf('71', plain,
% 0.38/0.60      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60         (k1_zfmisc_1 @ 
% 0.38/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | (v1_funct_1 @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('72', plain,
% 0.38/0.60      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60         (k1_zfmisc_1 @ 
% 0.38/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.38/0.60         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.60      inference('split', [status(esa)], ['71'])).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.38/0.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('74', plain,
% 0.38/0.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('split', [status(esa)], ['73'])).
% 0.38/0.60  thf('75', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('76', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('77', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | (m1_subset_1 @ 
% 0.38/0.60             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.60  thf('78', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | (m1_subset_1 @ 
% 0.38/0.60             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | (v2_struct_0 @ X10)
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X9))),
% 0.38/0.60      inference('simplify', [status(thm)], ['77'])).
% 0.38/0.60  thf('79', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.60               (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.60          | (m1_subset_1 @ 
% 0.38/0.60             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60              sk_D @ X1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['76', '78'])).
% 0.38/0.60  thf('80', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('81', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('82', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('83', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('87', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.60          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['79', '80', '81', '82', '83', '84', '85', '86'])).
% 0.38/0.60  thf('88', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('89', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.60          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['87', '88'])).
% 0.38/0.60  thf('90', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | (v2_struct_0 @ sk_D)
% 0.38/0.60        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.38/0.60           (k1_zfmisc_1 @ 
% 0.38/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | (v2_struct_0 @ sk_E)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['75', '89'])).
% 0.38/0.60  thf('91', plain,
% 0.38/0.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.60      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.60  thf('92', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('95', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('96', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | (v2_struct_0 @ sk_D)
% 0.38/0.60        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60           (k1_zfmisc_1 @ 
% 0.38/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['90', '91', '92', '93', '94', '95'])).
% 0.38/0.60  thf('97', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ sk_E)
% 0.38/0.60         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60            (k1_zfmisc_1 @ 
% 0.38/0.60             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60         | (v2_struct_0 @ sk_D)
% 0.38/0.60         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['74', '96'])).
% 0.38/0.60  thf('98', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60           (k1_zfmisc_1 @ 
% 0.38/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.60             sk_B)
% 0.38/0.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.38/0.60        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.60             sk_B)
% 0.38/0.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.38/0.60        | ~ (m1_subset_1 @ sk_C @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('99', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60           (k1_zfmisc_1 @ 
% 0.38/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.60      inference('split', [status(esa)], ['98'])).
% 0.38/0.60  thf('100', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_D)
% 0.38/0.60         | (v2_struct_0 @ sk_E)
% 0.38/0.60         | (v2_struct_0 @ sk_B)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['97', '99'])).
% 0.38/0.60  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('102', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['100', '101'])).
% 0.38/0.60  thf('103', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('104', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('clc', [status(thm)], ['102', '103'])).
% 0.38/0.60  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('106', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_D))
% 0.38/0.60         <= (~
% 0.38/0.60             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('clc', [status(thm)], ['104', '105'])).
% 0.38/0.60  thf('107', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('108', plain,
% 0.38/0.60      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.60         (k1_zfmisc_1 @ 
% 0.38/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.38/0.60       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['106', '107'])).
% 0.38/0.60  thf('109', plain,
% 0.38/0.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('split', [status(esa)], ['73'])).
% 0.38/0.60  thf('110', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('111', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('112', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | (v1_funct_2 @ 
% 0.38/0.60             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.38/0.60             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.60  thf('113', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | (v1_funct_2 @ 
% 0.38/0.60             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.38/0.60             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | (v2_struct_0 @ X10)
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X9))),
% 0.38/0.60      inference('simplify', [status(thm)], ['112'])).
% 0.38/0.60  thf('114', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.60               (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.60          | (v1_funct_2 @ 
% 0.38/0.60             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.60              sk_E @ X1) @ 
% 0.38/0.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.60          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['111', '113'])).
% 0.38/0.60  thf('115', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('116', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('117', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('118', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('119', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('122', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.60          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.38/0.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['114', '115', '116', '117', '118', '119', '120', '121'])).
% 0.38/0.60  thf('123', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('124', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.60             (k1_zfmisc_1 @ 
% 0.38/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_E)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.60          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.38/0.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.38/0.60          | (v2_struct_0 @ sk_D)
% 0.38/0.60          | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['122', '123'])).
% 0.38/0.60  thf('125', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | (v2_struct_0 @ sk_D)
% 0.38/0.60        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.38/0.60           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | (v2_struct_0 @ sk_E)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['110', '124'])).
% 0.38/0.60  thf('126', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('127', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.60  thf('128', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_E)))
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['126', '127'])).
% 0.38/0.60  thf('129', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('130', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_E))))),
% 0.38/0.60      inference('clc', [status(thm)], ['128', '129'])).
% 0.38/0.60  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('132', plain,
% 0.38/0.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.38/0.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.60            (u1_struct_0 @ sk_E)))),
% 0.38/0.60      inference('clc', [status(thm)], ['130', '131'])).
% 0.38/0.60  thf('133', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('134', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.38/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60                 sk_C @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['25', '26', '27', '28', '29', '30', '31'])).
% 0.38/0.60  thf('135', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_E)))
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['133', '134'])).
% 0.38/0.60  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('137', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60               sk_C @ (u1_struct_0 @ sk_E))))),
% 0.38/0.60      inference('clc', [status(thm)], ['135', '136'])).
% 0.38/0.60  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('139', plain,
% 0.38/0.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.60            (u1_struct_0 @ sk_E)))),
% 0.38/0.60      inference('clc', [status(thm)], ['137', '138'])).
% 0.38/0.60  thf('140', plain,
% 0.38/0.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.60      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.60  thf('141', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('143', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('144', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('145', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | (v2_struct_0 @ sk_D)
% 0.38/0.60        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)],
% 0.38/0.60                ['125', '140', '141', '142', '143', '144'])).
% 0.38/0.60  thf('146', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ sk_E)
% 0.38/0.60         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.60         | (v2_struct_0 @ sk_D)
% 0.38/0.60         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['109', '145'])).
% 0.38/0.60  thf('147', plain,
% 0.38/0.60      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('split', [status(esa)], ['98'])).
% 0.38/0.60  thf('148', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_D)
% 0.38/0.60         | (v2_struct_0 @ sk_E)
% 0.38/0.60         | (v2_struct_0 @ sk_B)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['146', '147'])).
% 0.38/0.60  thf('149', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('150', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['148', '149'])).
% 0.38/0.60  thf('151', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('152', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.60         <= (~
% 0.38/0.60             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('clc', [status(thm)], ['150', '151'])).
% 0.38/0.60  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('154', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_D))
% 0.38/0.60         <= (~
% 0.38/0.60             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('clc', [status(thm)], ['152', '153'])).
% 0.38/0.60  thf('155', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('156', plain,
% 0.38/0.60      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.60         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.60       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['154', '155'])).
% 0.38/0.60  thf('157', plain,
% 0.38/0.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.60      inference('split', [status(esa)], ['73'])).
% 0.38/0.60  thf('158', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('159', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('160', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | (v5_pre_topc @ 
% 0.38/0.60             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.38/0.60             X13 @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60                 (u1_struct_0 @ X9))))
% 0.38/0.60          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.60               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.60               (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (v1_funct_1 @ X12)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.60  thf('161', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X11)
% 0.38/0.60          | ~ (v2_pre_topc @ X11)
% 0.38/0.60          | ~ (l1_pre_topc @ X11)
% 0.38/0.60          | (v2_struct_0 @ X13)
% 0.38/0.60          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.60          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.60          | (v5_pre_topc @ 
% 0.38/0.60             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.38/0.60             X13 @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('simplify', [status(thm)], ['160'])).
% 0.38/0.61  thf('162', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.61               (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.61          | (v5_pre_topc @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.61              sk_D @ X1) @ 
% 0.38/0.61             sk_D @ X0)
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['159', '161'])).
% 0.38/0.61  thf('163', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('164', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('165', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('166', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('167', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('170', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ sk_D @ 
% 0.38/0.61             X0)
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['162', '163', '164', '165', '166', '167', '168', '169'])).
% 0.38/0.61  thf('171', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.61      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('172', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ sk_D @ 
% 0.38/0.61             X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['170', '171'])).
% 0.38/0.61  thf('173', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.38/0.61           sk_D @ sk_B)
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['158', '172'])).
% 0.38/0.61  thf('174', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.61  thf('175', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('178', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('179', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['173', '174', '175', '176', '177', '178'])).
% 0.38/0.61  thf('180', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['157', '179'])).
% 0.38/0.61  thf('181', plain,
% 0.38/0.61      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.61               sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('182', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v2_struct_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['180', '181'])).
% 0.38/0.61  thf('183', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('184', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['182', '183'])).
% 0.38/0.61  thf('185', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('186', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['184', '185'])).
% 0.38/0.61  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('188', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_D))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['186', '187'])).
% 0.38/0.61  thf('189', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('190', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.38/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['188', '189'])).
% 0.38/0.61  thf('191', plain,
% 0.38/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['73'])).
% 0.38/0.61  thf('192', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('193', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('194', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | (m1_subset_1 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.61  thf('195', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | (m1_subset_1 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('simplify', [status(thm)], ['194'])).
% 0.38/0.61  thf('196', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.61               (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.61          | (m1_subset_1 @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.61              sk_E @ X1) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['193', '195'])).
% 0.38/0.61  thf('197', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('198', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('199', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('200', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('201', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.61      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('202', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('204', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('205', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['196', '197', '198', '199', '200', '201', '202', '203', '204'])).
% 0.38/0.61  thf('206', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['192', '205'])).
% 0.38/0.61  thf('207', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('208', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('210', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('211', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('212', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['206', '207', '208', '209', '210', '211'])).
% 0.38/0.61  thf('213', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61            (k1_zfmisc_1 @ 
% 0.38/0.61             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['191', '212'])).
% 0.38/0.61  thf('214', plain,
% 0.38/0.61      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.38/0.61         <= (~
% 0.38/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('215', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v2_struct_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['213', '214'])).
% 0.38/0.61  thf('216', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('217', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['215', '216'])).
% 0.38/0.61  thf('218', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('219', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['217', '218'])).
% 0.38/0.61  thf('220', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('221', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_D))
% 0.38/0.61         <= (~
% 0.38/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['219', '220'])).
% 0.38/0.61  thf('222', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('223', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.38/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['221', '222'])).
% 0.38/0.61  thf('224', plain,
% 0.38/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['73'])).
% 0.38/0.61  thf('225', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('226', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('227', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | (v5_pre_topc @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.38/0.61             X10 @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.61  thf('228', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | (v5_pre_topc @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.38/0.61             X10 @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('simplify', [status(thm)], ['227'])).
% 0.38/0.61  thf('229', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.61               (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.61          | (v5_pre_topc @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.61              sk_E @ X1) @ 
% 0.38/0.61             sk_E @ X0)
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['226', '228'])).
% 0.38/0.61  thf('230', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('231', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('232', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('233', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('234', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.61      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('235', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('238', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ sk_E @ 
% 0.38/0.61             X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['229', '230', '231', '232', '233', '234', '235', '236', '237'])).
% 0.38/0.61  thf('239', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.38/0.61           sk_E @ sk_B)
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['225', '238'])).
% 0.38/0.61  thf('240', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('241', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('243', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('244', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('245', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['239', '240', '241', '242', '243', '244'])).
% 0.38/0.61  thf('246', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['224', '245'])).
% 0.38/0.61  thf('247', plain,
% 0.38/0.61      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.61               sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('248', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v2_struct_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['246', '247'])).
% 0.38/0.61  thf('249', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('250', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['248', '249'])).
% 0.38/0.61  thf('251', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('252', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['250', '251'])).
% 0.38/0.61  thf('253', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('254', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_D))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.61               sk_B)) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['252', '253'])).
% 0.38/0.61  thf('255', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('256', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.38/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['254', '255'])).
% 0.38/0.61  thf('257', plain,
% 0.38/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['73'])).
% 0.38/0.61  thf('258', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('259', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('260', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | (v1_funct_1 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.61  thf('261', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | (v1_funct_1 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('simplify', [status(thm)], ['260'])).
% 0.38/0.61  thf('262', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.61               (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.61          | (v1_funct_1 @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.61              sk_E @ X1))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['259', '261'])).
% 0.38/0.61  thf('263', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('264', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('265', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('266', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('267', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('268', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('269', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('270', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['262', '263', '264', '265', '266', '267', '268', '269'])).
% 0.38/0.61  thf('271', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.61      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('272', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1))
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['270', '271'])).
% 0.38/0.61  thf('273', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['258', '272'])).
% 0.38/0.61  thf('274', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('275', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('276', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('277', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('278', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('279', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['273', '274', '275', '276', '277', '278'])).
% 0.38/0.61  thf('280', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['257', '279'])).
% 0.38/0.61  thf('281', plain,
% 0.38/0.61      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('282', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v2_struct_0 @ sk_B)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['280', '281'])).
% 0.38/0.61  thf('283', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('284', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['282', '283'])).
% 0.38/0.61  thf('285', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('286', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['284', '285'])).
% 0.38/0.61  thf('287', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('288', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_D))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['286', '287'])).
% 0.38/0.61  thf('289', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('290', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.38/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['288', '289'])).
% 0.38/0.61  thf('291', plain,
% 0.38/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['73'])).
% 0.38/0.61  thf('292', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('293', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('294', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | (v1_funct_2 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.38/0.61             (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.61  thf('295', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | (v1_funct_2 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.38/0.61             (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('simplify', [status(thm)], ['294'])).
% 0.38/0.61  thf('296', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.61               (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.61          | (v1_funct_2 @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.61              sk_D @ X1) @ 
% 0.38/0.61             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['293', '295'])).
% 0.38/0.61  thf('297', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('298', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('299', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('300', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('301', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('302', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('303', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('304', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.61             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['296', '297', '298', '299', '300', '301', '302', '303'])).
% 0.38/0.61  thf('305', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.61      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('306', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.38/0.61             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['304', '305'])).
% 0.38/0.61  thf('307', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.38/0.61           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['292', '306'])).
% 0.38/0.61  thf('308', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.61  thf('309', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('310', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('311', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('312', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('313', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['307', '308', '309', '310', '311', '312'])).
% 0.38/0.61  thf('314', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['291', '313'])).
% 0.38/0.61  thf('315', plain,
% 0.38/0.61      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('316', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v2_struct_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['314', '315'])).
% 0.38/0.61  thf('317', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('318', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['316', '317'])).
% 0.38/0.61  thf('319', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('320', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['318', '319'])).
% 0.38/0.61  thf('321', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('322', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_D))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['320', '321'])).
% 0.38/0.61  thf('323', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('324', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['322', '323'])).
% 0.38/0.61  thf('325', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('326', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('327', plain, (((v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['325', '326'])).
% 0.38/0.61  thf('328', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('329', plain,
% 0.38/0.61      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('330', plain,
% 0.38/0.61      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['328', '329'])).
% 0.38/0.61  thf('331', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('332', plain,
% 0.38/0.61      ((~ (m1_subset_1 @ sk_C @ 
% 0.38/0.61           (k1_zfmisc_1 @ 
% 0.38/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.38/0.61         <= (~
% 0.38/0.61             ((m1_subset_1 @ sk_C @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('333', plain,
% 0.38/0.61      (((m1_subset_1 @ sk_C @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['331', '332'])).
% 0.38/0.61  thf('334', plain,
% 0.38/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['73'])).
% 0.38/0.61  thf('335', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('336', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('337', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | (v1_funct_1 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X11))),
% 0.38/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.38/0.61  thf('338', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X11)
% 0.38/0.61          | ~ (v2_pre_topc @ X11)
% 0.38/0.61          | ~ (l1_pre_topc @ X11)
% 0.38/0.61          | (v2_struct_0 @ X13)
% 0.38/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.38/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.38/0.61          | (v1_funct_1 @ 
% 0.38/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61                 (u1_struct_0 @ X9))))
% 0.38/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.38/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.38/0.61               (u1_struct_0 @ X9))
% 0.38/0.61          | ~ (v1_funct_1 @ X12)
% 0.38/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.38/0.61          | (v2_struct_0 @ X10)
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | ~ (v2_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('simplify', [status(thm)], ['337'])).
% 0.38/0.61  thf('339', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.38/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.38/0.61               (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.38/0.61          | (v1_funct_1 @ 
% 0.38/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.38/0.61              sk_D @ X1))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['336', '338'])).
% 0.38/0.61  thf('340', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('341', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('342', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('343', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('344', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('345', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('346', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('347', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1))
% 0.38/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['339', '340', '341', '342', '343', '344', '345', '346'])).
% 0.38/0.61  thf('348', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.38/0.61      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.61  thf('349', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.38/0.61          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1))
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['347', '348'])).
% 0.38/0.61  thf('350', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['335', '349'])).
% 0.38/0.61  thf('351', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.61  thf('352', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('353', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('354', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('355', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('356', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.38/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['350', '351', '352', '353', '354', '355'])).
% 0.38/0.61  thf('357', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['334', '356'])).
% 0.38/0.61  thf('358', plain,
% 0.38/0.61      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('359', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_D)
% 0.38/0.61         | (v2_struct_0 @ sk_E)
% 0.38/0.61         | (v2_struct_0 @ sk_B)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['357', '358'])).
% 0.38/0.61  thf('360', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('361', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['359', '360'])).
% 0.38/0.61  thf('362', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('363', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['361', '362'])).
% 0.38/0.61  thf('364', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('365', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_D))
% 0.38/0.61         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.38/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['363', '364'])).
% 0.38/0.61  thf('366', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('367', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.38/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['365', '366'])).
% 0.38/0.61  thf('368', plain,
% 0.38/0.61      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.38/0.61       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.38/0.61       ~ ((v1_funct_1 @ sk_C)) | 
% 0.38/0.61       ~ ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.61       ~
% 0.38/0.61       ((m1_subset_1 @ sk_C @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))) | 
% 0.38/0.61       ~
% 0.38/0.61       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.61       ~
% 0.38/0.61       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.38/0.61       ~
% 0.38/0.61       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.38/0.61       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.38/0.61       ~
% 0.38/0.61       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.38/0.61       ~
% 0.38/0.61       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.61       ~
% 0.38/0.61       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('369', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('370', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['369'])).
% 0.38/0.61  thf('371', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '370'])).
% 0.38/0.61  thf('372', plain,
% 0.38/0.61      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['72', '371'])).
% 0.38/0.61  thf('373', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('374', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('375', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.61  thf('376', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('377', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.38/0.61         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.38/0.61      inference('split', [status(esa)], ['376'])).
% 0.38/0.61  thf('378', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['73'])).
% 0.38/0.61  thf('379', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '378'])).
% 0.38/0.61  thf('380', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['377', '379'])).
% 0.38/0.61  thf('381', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.61  thf('382', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('383', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.38/0.61         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('split', [status(esa)], ['382'])).
% 0.38/0.61  thf('384', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('385', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['384'])).
% 0.38/0.61  thf('386', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '385'])).
% 0.38/0.61  thf('387', plain,
% 0.38/0.61      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.61        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['383', '386'])).
% 0.38/0.61  thf('388', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '37'])).
% 0.38/0.61  thf('389', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('390', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.61               sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['389'])).
% 0.38/0.61  thf('391', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('392', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['391'])).
% 0.38/0.61  thf('393', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '392'])).
% 0.38/0.61  thf('394', plain,
% 0.38/0.61      ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['390', '393'])).
% 0.38/0.61  thf('395', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('396', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('397', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.38/0.61         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.38/0.61      inference('split', [status(esa)], ['396'])).
% 0.38/0.61  thf('398', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('399', plain,
% 0.38/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['398'])).
% 0.38/0.61  thf('400', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '399'])).
% 0.38/0.61  thf('401', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['397', '400'])).
% 0.38/0.61  thf('402', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('403', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('404', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.38/0.61         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('split', [status(esa)], ['403'])).
% 0.38/0.61  thf('405', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('406', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['405'])).
% 0.38/0.61  thf('407', plain,
% 0.38/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '406'])).
% 0.38/0.61  thf('408', plain,
% 0.38/0.61      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['404', '407'])).
% 0.38/0.61  thf('409', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('410', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('411', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.38/0.61         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.38/0.61               sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['410'])).
% 0.38/0.61  thf('412', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('413', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['412'])).
% 0.38/0.61  thf('414', plain,
% 0.38/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '413'])).
% 0.38/0.61  thf('415', plain,
% 0.38/0.61      ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['411', '414'])).
% 0.38/0.61  thf('416', plain,
% 0.38/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.38/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['132', '139'])).
% 0.38/0.61  thf('417', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61        | (v1_funct_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('418', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.38/0.61         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.61      inference('split', [status(esa)], ['417'])).
% 0.38/0.61  thf('419', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('420', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.38/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('split', [status(esa)], ['419'])).
% 0.38/0.61  thf('421', plain,
% 0.38/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61         (k1_zfmisc_1 @ 
% 0.38/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368', '420'])).
% 0.38/0.61  thf('422', plain,
% 0.38/0.61      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['418', '421'])).
% 0.38/0.61  thf('423', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('424', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('425', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('426', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['70', '372', '373', '374', '375', '380', '381', '387', '388', 
% 0.38/0.61                 '394', '395', '401', '402', '408', '409', '415', '416', 
% 0.38/0.61                 '422', '423', '424', '425'])).
% 0.38/0.61  thf('427', plain,
% 0.38/0.61      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.38/0.61         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['98'])).
% 0.38/0.61  thf('428', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.38/0.61      inference('sat_resolution*', [status(thm)],
% 0.38/0.61                ['108', '156', '190', '223', '256', '290', '324', '327', 
% 0.38/0.61                 '330', '333', '367', '368'])).
% 0.38/0.61  thf('429', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.38/0.61      inference('simpl_trail', [status(thm)], ['427', '428'])).
% 0.38/0.61  thf('430', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_E)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['426', '429'])).
% 0.38/0.61  thf('431', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('432', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['430', '431'])).
% 0.38/0.61  thf('433', plain, (~ (v2_struct_0 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('434', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.38/0.61      inference('clc', [status(thm)], ['432', '433'])).
% 0.38/0.61  thf('435', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('436', plain, ((v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('clc', [status(thm)], ['434', '435'])).
% 0.38/0.61  thf('437', plain, ($false), inference('demod', [status(thm)], ['0', '436'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
